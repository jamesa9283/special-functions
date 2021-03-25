import ScholzeLog.logLemmas.ScholzeHelpLemmas
import ScholzeLog.logLemmas.tactics

notation `|`x`|` := abs x

open real set

lemma Schloze_log_nonsense (s t : ℝ) : 
  |s*log(|s|) + t*log(|t|) - (s + t)*log(|s + t|)| ≤ 2*log 2 * (|s| + |t|) :=
begin
  --have h_lambda := part1,
  -- I want to have wlog and then let s ≤ t. Now I can rewrite all of the s with a * t where |a| ≤ 1. 
  wlog Hst: s ≤ t,
  -- Now we want to derive the fact we can write s as a * t where |a| < 1
  have : ∀ (a ∈  Icc (-1 : ℝ) 1), s = a * t, 
  { intros a a_in,
    
    sorry

  },
  sorry
end

lemma Schloze_log_nonsense_nongeneral (s t : ℝ) (hs ∈ Icc (-1 : ℝ) 1) (ht : |t| = 1): 
  |s*log(|s|) + t*log(|t|) - (s + t)*log(|s + t|)| ≤ 2*log 2 * (|s| + |t|) :=
begin
  rw abs_eq at ht,
  swap, { norm_num,},
  cases ht with ht_one ht_neg,
  { rw ht_one,
    rw [one_mul, abs_one, log_one, add_zero],
    -- working on paper. HOW IS THIS SIMPLY ≤ 2log 2.
    -- I hate this and everything to do with this. 
    sorry},
  { sorry},
end

example (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1): |s*log(|s|) - (s + 1) * log(|s + 1|)| ≤ 2 * log 2 :=
begin
  -- PAIN
  -- This proof isn't that bad. I want to provide an argument relating to the fact that log is 
  -- monotonically increasing on s ∈ [0, 1]. The question now, is how?
    -- OK. So now I had an idea about using log x < log y → x < y, but it's a sum of logs.
  by_cases s_pos: 0 < s,
  { --apply log_stuff_pos s hs s_pos,
    sorry
  },
  { rw [not_lt] at s_pos,
    -- log time! Right I need to prove the other side now.
    --
    
    sorry
  }
end