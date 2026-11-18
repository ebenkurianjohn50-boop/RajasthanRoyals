#!/usr/bin/env Rscript

# Contextual Pressure and Reliability Model (CPRM)
# ------------------------------------------------
# End-to-end T20/T20I pressure ranking pipeline for the supplied data pack.
#
# Usage:
#   Rscript CPRM_pressure_rankings.R 6af3166e7b922_data_pack.zip outputs
#
# Required CRAN packages:
#   data.table, ranger, lme4, Matrix
#
# Outputs:
#   batter_rankings.csv
#   bowler_rankings.csv
#   batter_top10.csv
#   bowler_top10.csv
#   pressure_deliveries.csv.gz
#   model_diagnostics.csv
#   run_metadata.txt

options(stringsAsFactors = FALSE, warn = 1)

args <- commandArgs(trailingOnly = TRUE)
zip_path <- if (length(args) >= 1) args[[1]] else "C:/Users/HP/Downloads/6af3166e7b922_data_pack.zip"
out_dir  <- if (length(args) >= 2) args[[2]] else "outputs"
dir.create(out_dir, recursive = TRUE, showWarnings = FALSE)

required_packages <- c("data.table", "ranger", "lme4", "Matrix")
missing_packages <- required_packages[!vapply(required_packages, requireNamespace,
                                               logical(1), quietly = TRUE)]
if (length(missing_packages)) {
  stop(
    "Install required packages first:\n  install.packages(c(",
    paste(sprintf('"%s"', missing_packages), collapse = ", "), "))"
  )
}

suppressPackageStartupMessages({
  library(data.table)
  library(ranger)
  library(lme4)
})

set.seed(20261112)
options(datatable.print.nrows = 30)

log_message <- function(...) {
  cat(sprintf("[%s] %s\n", format(Sys.time(), "%H:%M:%S"), paste0(...)))
}

safe_divide <- function(x, y, default = 0) {
  ans <- rep(default, length(x))
  ok <- is.finite(x) & is.finite(y) & y != 0
  ans[ok] <- x[ok] / y[ok]
  ans
}

clip <- function(x, low = 0, high = 1) pmin(high, pmax(low, x))

percentile_rank <- function(x) {
  ok <- is.finite(x)
  ans <- rep(NA_real_, length(x))
  if (sum(ok) <= 1L) {
    ans[ok] <- 0.5
  } else {
    ans[ok] <- (frank(x[ok], ties.method = "average") - 1) / (sum(ok) - 1)
  }
  ans
}

zscore <- function(x, center = NULL, scale = NULL) {
  if (is.null(center)) center <- mean(x, na.rm = TRUE)
  if (is.null(scale)) scale <- stats::sd(x, na.rm = TRUE)
  if (!is.finite(scale) || scale < 1e-10) scale <- 1
  list(value = (x - center) / scale, center = center, scale = scale)
}

ewma_before <- function(x, lambda = 0.80) {
  x[!is.finite(x)] <- 0
  n <- length(x)
  if (!n) return(numeric())
  accumulated <- numeric(n)
  state <- 0
  for (i in seq_len(n)) {
    accumulated[i] <- state
    state <- lambda * state + x[i]
  }
  accumulated
}

locate_file <- function(root, filename) {
  hits <- list.files(root, pattern = paste0("^", filename, "$"), recursive = TRUE,
                     full.names = TRUE, ignore.case = TRUE)
  if (!length(hits)) stop("Missing required file in ZIP: ", filename)
  hits[[1]]
}

log_message("Extracting input pack")
if (!file.exists(zip_path)) stop("ZIP file not found: ", zip_path)
extract_dir <- tempfile("cprm_extract_")
dir.create(extract_dir)
on.exit(unlink(extract_dir, recursive = TRUE, force = TRUE), add = TRUE)
utils::unzip(zip_path, exdir = extract_dir)

balls <- fread(locate_file(extract_dir, "ball_by_ball.csv"), na.strings = c("", "NA"))
matches <- fread(locate_file(extract_dir, "matches.csv"), na.strings = c("", "NA"))
playing_xi <- fread(locate_file(extract_dir, "playing_eleven.csv"), na.strings = c("", "NA"))
competitions <- fread(locate_file(extract_dir, "competitions.csv"), na.strings = c("", "NA"))

required_ball_cols <- c(
  "match_id", "innings", "overid", "over_ball_num", "innings_ball_num",
  "batting_team_id", "bowling_team_id", "striker_id", "striker_name",
  "non_striker_id", "bowler_id", "bowler_name", "runs", "is_four", "is_six",
  "is_wicket", "dismissal_type", "dismissed_player_id", "extras_type",
  "extras1_runs", "extras_2_runs", "batting_type", "bowling_type", "pace_or_spin"
)
missing_cols <- setdiff(required_ball_cols, names(balls))
if (length(missing_cols)) stop("Missing ball-by-ball columns: ", paste(missing_cols, collapse = ", "))

log_message("Cleaning deliveries and reconstructing scoring")
balls[, source_row := .I]
balls[, match_id := as.integer(match_id)]
balls[, innings := as.integer(innings)]
balls[, match_key := paste(match_id, innings, sep = "_")]
balls[, extras_type_clean := fifelse(is.na(extras_type), "None", trimws(extras_type))]

# Data-pack-specific extras reconstruction:
# extras1_runs is a category code (1=no-ball, 2=wide, 3=leg-bye, 4=bye,
# 5=other, 6=none, 7=penalty), not a run amount. extras_2_runs stores runs
# beyond the base extra in a small subset of records.
balls[, base_extra := fcase(
  extras_type_clean == "Overstep", 1,
  extras_type_clean == "wide", 1,
  extras_type_clean == "legbyes", 1,
  extras_type_clean == "byes", 1,
  extras_type_clean == "other", 1,
  extras_type_clean == "Penalty", 5,
  default = 0
)]
balls[, extra_runs := base_extra + fifelse(is.na(extras_2_runs), 0, extras_2_runs)]
balls[, batter_runs := as.numeric(runs)]
balls[, team_runs := batter_runs + extra_runs]
balls[, legal_ball := !extras_type_clean %chin% c("wide", "Overstep")]
balls[, batter_ball_faced := extras_type_clean != "wide"]
balls[, bowler_runs := fifelse(
  extras_type_clean %chin% c("byes", "legbyes"),
  0,
  team_runs
)]

bowler_wicket_types <- c("Caught", "Bowled", "LBW", "Stump", "Stumped", "Hit Wicket")
balls[, team_wicket := as.integer(is_wicket %in% TRUE)]
balls[, bowler_wicket := as.integer(is_wicket %in% TRUE & dismissal_type %chin% bowler_wicket_types)]
balls[, runout_or_fielding_wicket := as.integer(is_wicket %in% TRUE & !bowler_wicket)]

# Sort by the supplied delivery order. source_row breaks any ties on illegal balls.
setorder(balls, match_id, innings, innings_ball_num, source_row)
balls[, delivery_index := seq_len(.N), by = .(match_id, innings)]

# Match metadata.
matches[, match_date := as.IDate(match_date)]
match_fields <- intersect(c(
  "match_id", "comp_id", "match_date", "stage", "venue_id", "venue_country",
  "first_inn_revised_overs", "second_inn_revised_overs", "revised_target",
  "knock_out", "win_team_id", "result"
), names(matches))
balls <- merge(balls, matches[, match_fields, with = FALSE], by = "match_id", all.x = TRUE, sort = FALSE)
comp_fields <- intersect(c("comp_id", "comp_name", "match_format", "season"), names(competitions))
balls <- merge(balls, competitions[, comp_fields, with = FALSE], by = "comp_id", all.x = TRUE, sort = FALSE)
setorder(balls, match_id, innings, delivery_index)

# Remove innings that are outside normal T20 play. Retain innings 1 and 2 only.
balls <- balls[innings %in% c(1L, 2L)]

# Pre-ball cumulative state.
balls[, score_before := shift(cumsum(team_runs), fill = 0), by = .(match_id, innings)]
balls[, wickets_before := shift(cumsum(team_wicket), fill = 0), by = .(match_id, innings)]
balls[, legal_balls_before := shift(cumsum(as.integer(legal_ball)), fill = 0),
      by = .(match_id, innings)]
balls[, score_after := score_before + team_runs]
balls[, wickets_after := wickets_before + team_wicket]
balls[, legal_balls_after := legal_balls_before + as.integer(legal_ball)]

# Final innings score and target.
innings_summary <- balls[, .(
  innings_final_score = max(score_after, na.rm = TRUE),
  innings_legal_balls = max(legal_balls_after, na.rm = TRUE)
), by = .(match_id, innings)]
first_innings <- innings_summary[innings == 1L,
  .(match_id, first_innings_score = innings_final_score)]
balls <- merge(balls, first_innings, by = "match_id", all.x = TRUE, sort = FALSE)
setorder(balls, match_id, innings, delivery_index)

balls[, scheduled_balls := 120L]
balls[innings == 1L & is.finite(first_inn_revised_overs),
      scheduled_balls := as.integer(round(first_inn_revised_overs * 6))]
balls[innings == 2L & is.finite(second_inn_revised_overs),
      scheduled_balls := as.integer(round(second_inn_revised_overs * 6))]
balls[, balls_remaining := pmax(0L, scheduled_balls - legal_balls_before)]
balls[, wickets_remaining := pmax(0L, 10L - wickets_before)]
balls[, target := fifelse(
  innings == 2L,
  fifelse(is.finite(revised_target), as.numeric(revised_target), first_innings_score + 1),
  NA_real_
)]
balls[, runs_required := fifelse(innings == 2L, pmax(0, target - score_before), 0)]
balls[, required_rr := fifelse(
  innings == 2L & balls_remaining > 0,
  6 * runs_required / balls_remaining,
  0
)]
balls[, current_rr := 6 * safe_divide(score_before, legal_balls_before, 0)]
balls[, rr_gap := fifelse(innings == 2L, required_rr - current_rr, 0)]
balls[, phase := fcase(
  legal_balls_before < 36, "Powerplay",
  legal_balls_before < 90, "Middle",
  default = "Death"
)]

# Batter pre-ball state.
balls[, batter_runs_before := shift(cumsum(batter_runs), fill = 0),
      by = .(match_id, innings, striker_id)]
balls[, batter_balls_before := shift(cumsum(as.integer(batter_ball_faced)), fill = 0),
      by = .(match_id, innings, striker_id)]
balls[, batter_sr_before := 100 * safe_divide(batter_runs_before, batter_balls_before, 0)]

# Bowler pre-ball state.
balls[, bowler_runs_before := shift(cumsum(bowler_runs), fill = 0),
      by = .(match_id, innings, bowler_id)]
balls[, bowler_legal_before := shift(cumsum(as.integer(legal_ball)), fill = 0),
      by = .(match_id, innings, bowler_id)]
balls[, bowler_econ_before := 6 * safe_divide(bowler_runs_before, bowler_legal_before, 0)]
balls[, current_over_runs_before := shift(cumsum(bowler_runs), fill = 0),
      by = .(match_id, innings, bowler_id, overid)]

# Match-result outcome from the current batting side's perspective.
balls[, batting_team_win := as.integer(is.finite(win_team_id) & win_team_id == batting_team_id)]
valid_results <- balls[is.finite(win_team_id) & !grepl("No Result|Abandoned", result, ignore.case = TRUE)]
if (uniqueN(valid_results$match_id) < 100) stop("Too few completed matches after result cleaning")

# Basic score audit. The script reports but does not invent unavailable scorecards.
audit <- data.table(
  metric = c("delivery_rows", "matches_with_deliveries", "completed_matches_used",
             "innings_over_10_wickets", "negative_runs", "illegal_ball_share"),
  value = c(
    nrow(balls), uniqueN(balls$match_id), uniqueN(valid_results$match_id),
    uniqueN(balls[wickets_after > 10, match_key]),
    sum(balls$team_runs < 0, na.rm = TRUE),
    mean(!balls$legal_ball, na.rm = TRUE)
  )
)
fwrite(audit, file.path(out_dir, "data_audit.csv"))
if (audit[metric == "innings_over_10_wickets", value] > 0) {
  warning("Some innings exceed ten reconstructed wickets; inspect data_audit.csv")
}

log_message("Creating time-blocked cross-validation folds")
match_order <- unique(valid_results[, .(match_id, match_date)])
setorder(match_order, match_date, match_id)
match_order[, time_rank := frank(match_date, ties.method = "average") / .N]
match_order[, fold := pmin(5L, pmax(1L, ceiling(5 * time_rank)))]
balls <- merge(balls, match_order[, .(match_id, fold)], by = "match_id", all.x = TRUE, sort = FALSE)
setorder(balls, match_id, innings, delivery_index)

# Stable modelling variables.
factor_vars <- c("innings", "phase", "venue_country", "match_format",
                 "batting_type", "bowling_type", "pace_or_spin")
for (v in intersect(factor_vars, names(balls))) {
  balls[, (v) := factor(fifelse(is.na(get(v)), "Unknown", as.character(get(v))))]
}

numeric_features <- c(
  "score_before", "wickets_before", "balls_remaining", "wickets_remaining",
  "runs_required", "required_rr", "current_rr", "rr_gap",
  "batter_runs_before", "batter_balls_before", "batter_sr_before",
  "bowler_runs_before", "bowler_legal_before", "bowler_econ_before",
  "current_over_runs_before", "knock_out"
)
categorical_features <- intersect(factor_vars, names(balls))
model_features <- c(numeric_features, categorical_features)

for (v in numeric_features) {
  if (!v %in% names(balls)) balls[, (v) := 0]
  balls[!is.finite(get(v)), (v) := 0]
}

fit_ranger <- function(train, response, features, probability = FALSE,
                       num_trees = 500L, min_node_size = 30L) {
  f <- as.formula(paste(response, "~", paste(features, collapse = " + ")))
  ranger(
    formula = f,
    data = as.data.frame(train[, c(response, features), with = FALSE]),
    probability = probability,
    num.trees = num_trees,
    min.node.size = min_node_size,
    mtry = max(2L, floor(sqrt(length(features)))),
    importance = "impurity",
    respect.unordered.factors = "order",
    seed = 20261112,
    num.threads = max(1L, parallel::detectCores(logical = FALSE) - 1L)
  )
}

predict_ranger_numeric <- function(model, newdata) {
  as.numeric(predict(model, data = as.data.frame(newdata))$predictions)
}

predict_ranger_probability <- function(model, newdata, positive_class = "1") {
  p <- predict(model, data = as.data.frame(newdata))$predictions
  if (is.null(dim(p))) return(as.numeric(p))
  if (!positive_class %in% colnames(p)) stop("Positive class missing from probability model")
  as.numeric(p[, positive_class])
}

# Cross-fitted expected runs. These models deliberately exclude player IDs; the
# prediction is a contextual benchmark, not the player's own historical mean.
log_message("Cross-fitting expected batter and bowler runs")
balls[, expected_batter_runs := NA_real_]
balls[, expected_bowler_runs := NA_real_]

completed_rows <- which(is.finite(balls$fold) & is.finite(balls$win_team_id))
for (f in 2:5) {
  test_idx <- which(balls$fold == f & seq_len(nrow(balls)) %in% completed_rows)
  train_idx <- which(balls$fold < f & is.finite(balls$fold) & is.finite(balls$win_team_id))
  if (!length(test_idx) || !length(train_idx)) next
  train <- balls[train_idx]
  test <- balls[test_idx]

  batter_model <- fit_ranger(train, "batter_runs", model_features,
                             probability = FALSE, num_trees = 350L, min_node_size = 40L)
  bowler_model <- fit_ranger(train, "bowler_runs", model_features,
                             probability = FALSE, num_trees = 350L, min_node_size = 40L)
  balls[test_idx, expected_batter_runs := clip(
    predict_ranger_numeric(batter_model, test[, model_features, with = FALSE]), 0, 6)]
  balls[test_idx, expected_bowler_runs := clip(
    predict_ranger_numeric(bowler_model, test[, model_features, with = FALSE]), 0, 7)]
  rm(batter_model, bowler_model, train, test); gc(FALSE)
}

# Fill excluded/no-result rows from completed-sample averages only for sequence
# construction. These rows never enter the final player models.
balls[!is.finite(expected_batter_runs), expected_batter_runs :=
        mean(balls$expected_batter_runs, na.rm = TRUE)]
balls[!is.finite(expected_bowler_runs), expected_bowler_runs :=
        mean(balls$expected_bowler_runs, na.rm = TRUE)]

balls[, batter_run_debt_event := expected_batter_runs - batter_runs]
balls[, bowler_concession_event := bowler_runs - expected_bowler_runs]
balls[, batter_sequence_raw := ewma_before(batter_run_debt_event, 0.80),
      by = .(match_id, innings, striker_id)]
balls[, bowler_sequence_raw := ewma_before(bowler_concession_event, 0.80),
      by = .(match_id, innings, bowler_id)]
balls[, batter_sequence_raw := pmax(0, batter_sequence_raw)]
balls[, bowler_sequence_raw := pmax(0, bowler_sequence_raw)]

# Cross-fitted win-probability models. Separate models are used by innings.
log_message("Cross-fitting win-probability models")
wp_features <- c(model_features, "expected_batter_runs", "expected_bowler_runs")
balls[, wp_before := NA_real_]
wp_models_by_fold <- lapply(1:2, function(x) vector("list", 5))

for (inn in 1:2) {
  for (f in 2:5) {
    test_idx <- which(balls$innings == inn & balls$fold == f & is.finite(balls$win_team_id))
    train_idx <- which(balls$innings == inn & balls$fold < f &
                         is.finite(balls$fold) & is.finite(balls$win_team_id))
    if (!length(test_idx) || !length(train_idx)) next
    train <- copy(balls[train_idx])
    test <- balls[test_idx]
    train[, wp_target := factor(batting_team_win, levels = c(0, 1))]
    wp_model <- fit_ranger(train, "wp_target", wp_features,
                           probability = TRUE, num_trees = 600L, min_node_size = 50L)
    balls[test_idx, wp_before := clip(
      predict_ranger_probability(wp_model, test[, wp_features, with = FALSE]), 0.001, 0.999)]
    wp_models_by_fold[[inn]][[f]] <- wp_model
    rm(train, test); gc(FALSE)
  }
}

if (mean(is.finite(balls$wp_before[balls$fold >= 2]), na.rm = TRUE) < 0.95) {
  stop("Rolling-origin win-probability fitting did not cover enough evaluation deliveries")
}

# Empirical outcome probabilities by innings/phase/wickets band. This is more
# stable and auditable than fitting a large multiclass model for sparse outcomes.
balls[, outcome := fcase(
  team_wicket == 1L, "W",
  extras_type_clean == "wide", "Wd",
  extras_type_clean == "Overstep", "Nb",
  team_runs >= 6, "6",
  team_runs >= 4, "4",
  team_runs == 3, "3",
  team_runs == 2, "2",
  team_runs == 1, "1",
  default = "0"
)]
outcome_levels <- c("0", "1", "2", "3", "4", "6", "W", "Wd", "Nb")
balls[, wicket_band := cut(wickets_before, breaks = c(-Inf, 2, 5, Inf),
                           labels = c("0-2", "3-5", "6+"))]
outcome_probs <- balls[is.finite(win_team_id), .N,
                       by = .(innings, phase, wicket_band, outcome)]
outcome_probs[, probability := N / sum(N), by = .(innings, phase, wicket_band)]

global_probs <- balls[is.finite(win_team_id), .N, by = outcome]
global_probs[, global_probability := N / sum(N)]

simulate_state <- function(dt, outcome_name) {
  x <- copy(dt)
  run_add <- switch(outcome_name,
    "0" = 0, "1" = 1, "2" = 2, "3" = 3, "4" = 4, "6" = 6,
    "W" = 0, "Wd" = 1, "Nb" = 1, 0
  )
  wicket_add <- as.integer(outcome_name == "W")
  legal_add <- as.integer(!outcome_name %in% c("Wd", "Nb"))
  x[, score_before := score_before + run_add]
  x[, wickets_before := pmin(10, wickets_before + wicket_add)]
  x[, wickets_remaining := pmax(0, 10 - wickets_before)]
  x[, balls_remaining := pmax(0, balls_remaining - legal_add)]
  x[, legal_balls_before := legal_balls_before + legal_add]
  x[, runs_required := fifelse(innings == 2L, pmax(0, target - score_before), 0)]
  x[, required_rr := fifelse(innings == 2L & balls_remaining > 0,
                             6 * runs_required / balls_remaining, 0)]
  x[, current_rr := 6 * safe_divide(score_before, legal_balls_before, 0)]
  x[, rr_gap := fifelse(innings == 2L, required_rr - current_rr, 0)]
  x[, batter_runs_before := batter_runs_before + fifelse(outcome_name %in% c("Wd", "Nb"), 0, run_add)]
  x[, batter_balls_before := batter_balls_before + as.integer(outcome_name != "Wd")]
  x[, batter_sr_before := 100 * safe_divide(batter_runs_before, batter_balls_before, 0)]
  x[, bowler_runs_before := bowler_runs_before + run_add]
  x[, bowler_legal_before := bowler_legal_before + legal_add]
  x[, bowler_econ_before := 6 * safe_divide(bowler_runs_before, bowler_legal_before, 0)]
  x[, current_over_runs_before := current_over_runs_before + run_add]
  x
}

log_message("Simulating counterfactual delivery outcomes")
model_rows <- balls[is.finite(wp_before) & is.finite(fold)]
model_rows[, row_key := .I]

prob_grid <- CJ(row_key = model_rows$row_key, outcome = outcome_levels)
prob_grid <- merge(prob_grid,
  model_rows[, .(row_key, innings, phase, wicket_band)], by = "row_key", all.x = TRUE)
prob_grid <- merge(prob_grid,
  outcome_probs[, .(innings, phase, wicket_band, outcome, probability)],
  by = c("innings", "phase", "wicket_band", "outcome"), all.x = TRUE)
prob_grid <- merge(prob_grid, global_probs[, .(outcome, global_probability)],
                   by = "outcome", all.x = TRUE)
prob_grid[!is.finite(probability), probability := global_probability]
prob_grid[, probability := probability / sum(probability), by = row_key]

model_rows[, `:=`(match_stakes_raw = 0, batter_constraint_raw = 0,
                  bowler_constraint_raw = 0, expected_wp_delta = 0,
                  actual_wp_after = NA_real_)]

delta_threshold <- 0.02
actual_outcome_map <- model_rows$outcome

for (o in outcome_levels) {
  cf <- simulate_state(model_rows, o)
  wp_after_o <- numeric(nrow(cf))
  for (inn in 1:2) {
    for (f in 2:5) {
      idx <- which(cf$innings == inn & cf$fold == f)
      if (length(idx)) {
        wp_after_o[idx] <- clip(predict_ranger_probability(
          wp_models_by_fold[[inn]][[f]], cf[idx, wp_features, with = FALSE]), 0.001, 0.999)
      }
    }
  }
  p_o <- prob_grid[outcome == o][match(model_rows$row_key, row_key), probability]
  delta_o <- wp_after_o - model_rows$wp_before
  model_rows[, match_stakes_raw := match_stakes_raw + p_o * abs(delta_o)]
  model_rows[, expected_wp_delta := expected_wp_delta + p_o * delta_o]
  model_rows[, batter_constraint_raw := batter_constraint_raw +
               p_o * as.numeric(delta_o < -delta_threshold)]
  model_rows[, bowler_constraint_raw := bowler_constraint_raw +
               p_o * as.numeric(delta_o > delta_threshold)]
  actual_idx <- which(actual_outcome_map == o)
  if (length(actual_idx)) model_rows[actual_idx, actual_wp_after := wp_after_o[actual_idx]]
  rm(cf, wp_after_o, p_o, delta_o); gc(FALSE)
}

model_rows[, actual_wp_delta := actual_wp_after - wp_before]

# Role-specific performance attribution. Run-outs/fielding wickets are excluded
# from the bowler model; byes and leg-byes do not count against the bowler.
model_rows[, batter_performance := actual_wp_delta - expected_wp_delta]
model_rows[, bowler_performance := -(actual_wp_delta - expected_wp_delta)]
model_rows[runout_or_fielding_wicket == 1L, bowler_performance := NA_real_]
model_rows[extras_type_clean %chin% c("byes", "legbyes"), bowler_performance := NA_real_]
model_rows[extras_type_clean == "wide", batter_performance := NA_real_]

# Responsibility proxies based only on fields available before the delivery.
batting_order_map <- playing_xi[is_played %in% TRUE,
  .(match_id, team_id, player_id, listed_batting_order = as.numeric(batting_order))]
model_rows <- merge(model_rows, batting_order_map,
  by.x = c("match_id", "batting_team_id", "striker_id"),
  by.y = c("match_id", "team_id", "player_id"), all.x = TRUE, sort = FALSE)
setorder(model_rows, match_id, innings, delivery_index)
model_rows[!is.finite(listed_batting_order), listed_batting_order := 7]

model_rows[, batter_responsibility_raw := rowMeans(cbind(
  clip(batter_balls_before / 20),
  clip(wickets_before / 7),
  as.numeric(listed_batting_order <= 6 & wickets_remaining <= 4)
))]

# Bowler responsibility is a transparent observable proxy: late-phase assignment,
# a close chase, and use of a bowler with limited legal deliveries remaining.
model_rows[, bowler_responsibility_raw := rowMeans(cbind(
  as.numeric(phase == "Death"),
  clip(bowler_legal_before / 24),
  as.numeric(innings == 2L & balls_remaining <= 24)
))]

# Normalize each dimension. Stakes are normalized separately by innings because
# first-innings win probability is inherently less target-specific.
model_rows[, match_stakes := percentile_rank(match_stakes_raw), by = innings]
model_rows[, batter_constraint := percentile_rank(batter_constraint_raw), by = innings]
model_rows[, bowler_constraint := percentile_rank(bowler_constraint_raw), by = innings]
model_rows[, batter_sequence := percentile_rank(batter_sequence_raw), by = innings]
model_rows[, bowler_sequence := percentile_rank(bowler_sequence_raw), by = innings]
model_rows[, batter_responsibility := percentile_rank(batter_responsibility_raw), by = innings]
model_rows[, bowler_responsibility := percentile_rank(bowler_responsibility_raw), by = innings]

# A descriptive index is exported for charts only. It is not used to rank players.
# The rankings use all four dimensions directly in the hierarchical model.
model_rows[, batter_pressure_descriptive :=
  rowMeans(cbind(match_stakes, batter_constraint, batter_sequence,
                 batter_responsibility), na.rm = TRUE)]
model_rows[, bowler_pressure_descriptive :=
  rowMeans(cbind(match_stakes, bowler_constraint, bowler_sequence,
                 bowler_responsibility), na.rm = TRUE)]

fit_player_model <- function(dt, role = c("batter", "bowler")) {
  role <- match.arg(role)
  if (role == "batter") {
    response <- "batter_performance"
    player_id <- "striker_id"
    player_name <- "striker_name"
    constraint <- "batter_constraint"
    sequence <- "batter_sequence"
    responsibility <- "batter_responsibility"
    exposure_ball <- "batter_ball_faced"
  } else {
    response <- "bowler_performance"
    player_id <- "bowler_id"
    player_name <- "bowler_name"
    constraint <- "bowler_constraint"
    sequence <- "bowler_sequence"
    responsibility <- "bowler_responsibility"
    exposure_ball <- "legal_ball"
  }

  d <- copy(dt[is.finite(get(response)) & get(exposure_ball) %in% TRUE])
  setnames(d, c(player_id, player_name, constraint, sequence, responsibility),
           c("player_id", "player_name", "constraint", "sequence", "responsibility"))
  d[, player_id := factor(player_id)]

  # Eligibility is applied after fitting so partial pooling can use the full population.
  counts <- d[, .(
    total_balls = .N,
    innings_count = uniqueN(paste(match_id, innings)),
    match_count = uniqueN(match_id),
    pressure_balls = sum(match_stakes >= 0.80, na.rm = TRUE),
    pressure_matches = uniqueN(match_id[match_stakes >= 0.80]),
    player_name = names(sort(table(player_name), decreasing = TRUE))[1]
  ), by = player_id]

  fixed_formula <- paste0(
    response,
    " ~ match_stakes + constraint + sequence + responsibility + innings + phase"
  )
  random_formula <- "(1 + match_stakes + constraint + sequence + responsibility || player_id)"
  formula_full <- as.formula(paste(fixed_formula, random_formula, sep = " + "))

  control <- lmerControl(
    optimizer = "bobyqa",
    optCtrl = list(maxfun = 200000),
    check.conv.singular = "ignore"
  )
  model <- try(lmer(formula_full, data = d, REML = TRUE, control = control), silent = TRUE)
  if (inherits(model, "try-error") || isSingular(model, tol = 1e-4)) {
    warning(role, " full random-slope model was singular; using reduced random slopes")
    formula_reduced <- as.formula(paste(
      fixed_formula,
      "(1 + match_stakes + sequence || player_id)", sep = " + "
    ))
    model <- lmer(formula_reduced, data = d, REML = TRUE, control = control)
  }

  # Reference environment: the observed distribution among top-quintile stakes,
  # evaluated identically for every player. Limit the grid for memory efficiency.
  reference <- copy(d[match_stakes >= 0.80])
  if (nrow(reference) > 5000) reference <- reference[sample(.N, 5000)]
  reference[, player_id := factor(levels(d$player_id)[1], levels = levels(d$player_id))]

  rank_rows <- vector("list", nlevels(d$player_id))
  residual_sigma <- sigma(model)
  for (j in seq_along(levels(d$player_id))) {
    pid <- levels(d$player_id)[j]
    reference[, player_id := factor(pid, levels = levels(d$player_id))]
    pred <- predict(model, newdata = reference, allow.new.levels = FALSE)
    pressure_rating <- mean(pred, na.rm = TRUE)
    n_pressure <- counts[player_id == pid, pressure_balls]
    uncertainty <- residual_sigma / sqrt(max(1, n_pressure))
    rank_rows[[j]] <- data.table(
      player_id = pid,
      pressure_rating = pressure_rating,
      uncertainty_penalty = 1.28 * uncertainty,
      conservative_rating = pressure_rating - 1.28 * uncertainty
    )
  }

  ratings <- rbindlist(rank_rows)
  ratings <- merge(ratings, counts, by = "player_id", all.x = TRUE)
  ratings[, eligible := total_balls >= 250 & pressure_balls >= 60 &
            innings_count >= 15 & pressure_matches >= 8]
  setorder(ratings, -eligible, -conservative_rating)
  ratings[, overall_rank := frank(-conservative_rating, ties.method = "first"),
          by = eligible]
  ratings[eligible == TRUE, eligible_rank := seq_len(.N)]

  list(model = model, ratings = ratings, analysis_data = d)
}

log_message("Fitting hierarchical batter model")
batter_fit <- fit_player_model(model_rows, "batter")
log_message("Fitting hierarchical bowler model")
bowler_fit <- fit_player_model(model_rows, "bowler")

batter_rankings <- batter_fit$ratings
bowler_rankings <- bowler_fit$ratings

fwrite(batter_rankings, file.path(out_dir, "batter_rankings.csv"))
fwrite(bowler_rankings, file.path(out_dir, "bowler_rankings.csv"))
fwrite(head(batter_rankings[eligible == TRUE][order(eligible_rank)], 10),
       file.path(out_dir, "batter_top10.csv"))
fwrite(head(bowler_rankings[eligible == TRUE][order(eligible_rank)], 10),
       file.path(out_dir, "bowler_top10.csv"))

# Calibration diagnostics.
diagnostics <- model_rows[, .(
  n = .N,
  observed_win_rate = mean(batting_team_win, na.rm = TRUE),
  predicted_win_rate = mean(wp_before, na.rm = TRUE),
  brier_score = mean((wp_before - batting_team_win)^2, na.rm = TRUE),
  mean_match_stakes = mean(match_stakes_raw, na.rm = TRUE)
), by = .(innings, wp_decile = cut(wp_before, breaks = seq(0, 1, 0.1),
                                   include.lowest = TRUE))]
fwrite(diagnostics, file.path(out_dir, "model_diagnostics.csv"))

# Export the modelling table without raw text-heavy columns.
export_cols <- intersect(c(
  "match_id", "match_date", "innings", "overid", "over_ball_num",
  "striker_id", "striker_name", "bowler_id", "bowler_name",
  "score_before", "wickets_before", "balls_remaining", "runs_required",
  "required_rr", "wp_before", "match_stakes", "batter_constraint",
  "bowler_constraint", "batter_sequence", "bowler_sequence",
  "batter_responsibility", "bowler_responsibility",
  "batter_performance", "bowler_performance"
), names(model_rows))
fwrite(model_rows[, export_cols, with = FALSE], file.path(out_dir, "pressure_deliveries.csv.gz"))

saveRDS(batter_fit$model, file.path(out_dir, "batter_hierarchical_model.rds"))
saveRDS(bowler_fit$model, file.path(out_dir, "bowler_hierarchical_model.rds"))

metadata <- c(
  paste("Run time:", Sys.time()),
  paste("Input ZIP:", normalizePath(zip_path)),
  paste("Deliveries modelled:", nrow(model_rows)),
  paste("Matches modelled:", uniqueN(model_rows$match_id)),
  paste("Eligible batters:", sum(batter_rankings$eligible, na.rm = TRUE)),
  paste("Eligible bowlers:", sum(bowler_rankings$eligible, na.rm = TRUE)),
  "Primary ranking: hierarchical predicted value in a common top-quintile match-stakes reference set",
  "Uncertainty adjustment: rating minus 1.28 * residual standard error / sqrt(pressure balls)",
  "Responsibility variables are observable proxies, not direct measurements of psychology."
)
writeLines(metadata, file.path(out_dir, "run_metadata.txt"))

cat("\nTop 10 batters under pressure\n")
print(head(batter_rankings[eligible == TRUE][order(eligible_rank)], 10)[,
  .(rank = eligible_rank, player_name, conservative_rating, pressure_balls,
    pressure_matches)])
cat("\nTop 10 bowlers under pressure\n")
print(head(bowler_rankings[eligible == TRUE][order(eligible_rank)], 10)[,
  .(rank = eligible_rank, player_name, conservative_rating, pressure_balls,
    pressure_matches)])
cat("\nFiles written to: ", normalizePath(out_dir), "\n", sep = "")
