import .tactics .ScholzeHelpLemmas

open real

example (s : ℝ) (h : 0 < s) : 4*s^s = exp(log 4 + s*log s) :=
begin
  rw [exp_add, exp_log (show 0 < (4 : ℝ), by norm_num), ← log_rpow h, exp_log],
  apply rpow_pos_of_pos,
  linarith,
end

example (s : ℝ) (h : 0 < s) : (s+1)^(s+1) = exp((s+1) * log(s+1)) :=
begin
  rw ← log_rpow (show 0 < s+1, by linarith),
  rw exp_log,
  apply rpow_pos_of_pos,
  linarith
end