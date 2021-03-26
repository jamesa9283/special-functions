import ScholzeLog.logLemmas.ScholzeHelpLemmas
import ScholzeLog.logLemmas.tactics

import tactic

/- In this file we prove Schloze Lemma 5.3 from https://www.math.uni-bonn.de/people/scholze/Analytic.pdf -/

notation `|`x`|` := abs x

open real set

lemma part1 (s t l : ℝ) (hl : 0 < l) : |l*s*log (|l * s|) + l*t*log(|l*t|) - (l*s + l*t)*log(|l*s + l*t|)| 
    = l * |s*log(|s|) + t*log(|t|) - (s + t)*log(|s + t|)| :=
begin
  conv_rhs { rw [← abs_of_pos hl, ← abs_mul]},
  congr',
  simp only [log_mul', ← mul_add, mul_assoc, log_mul' hl, log_abs],
  ring,
end

lemma part2_1 (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) (s_pos : 0 < s): |s*log(|s|) - (s + 1) * log(|s + 1|)| ≤ 2 * log 2 :=
begin
  have hS_pos : 0 < (s ^ s / (s + 1) ^ (s + 1)), -- true
  { rw [lt_div_iff, zero_mul];
    {apply rpow_pos_of_pos,
      linarith},
  },
  have hS_nonneg : 0 ≤ (s + 1)^s,
  { apply le_of_lt,
    apply rpow_pos_of_pos,
    linarith,},
    have hS_le_one : (s ^ s / (s + 1) ^ (s + 1)) < 1, -- true. I think.
  { rw div_lt_one,
    have hs_lt : s^s < (s+1)^s := rpow_lt_rpow (le_of_lt s_pos) 
      (show s < s+1, by linarith) s_pos,
    rw rpow_add (show 0 < s + 1, by linarith),
    rw rpow_one,
    have one_lt_s_add_one : 1 < s + 1 := by linarith,
    have := mul_lt_mul hs_lt (le_of_lt one_lt_s_add_one) (by norm_num)
      (hS_nonneg),
    rwa mul_one at this,
    { apply rpow_pos_of_pos,
    linarith,}
  },
  { --have logle := log_lt_log_iff (s_pos),
    --rw log_
    simp only [log_abs, ← log_rpow s_pos, ← log_rpow (show 0 < s + 1, by linarith)],
    rw ← log_div _ _, -- (*) (**)
    { have h_num : 2 * log 2 = log 4,
      { rw ← log_rpow,
        congr,
        rw [show (2 : ℝ) ^ (2 : ℝ) = 2 ^ ((2 : ℕ) : ℝ), by norm_cast, rpow_nat_cast];
        norm_num,
        norm_num,
      }, 
      rw [← Icc_def, mem_set_of_eq] at hs,
      have log_stuff_neg := log_neg (hS_pos) (hS_le_one),  
      -- -log (s ^ s / (s + 1) ^ (s + 1)) ≤ 2 * log 2
      rw [abs_of_neg (log_stuff_neg), ← log_inv, inv_div, h_num, log_le_log _ _],
      { 
        { rw div_le_iff,   
          { have pow_to_exp1 : 4*s^s = exp(log 4 + s*log s),
            { rw [exp_add, exp_log (show 0 < (4 : ℝ), by norm_num), ← log_rpow s_pos, exp_log],
              apply rpow_pos_of_pos,
              linarith},
            have pow_to_exp2 : (s+1)^(s+1) = exp((s+1) * log(s+1)),
            { rw [← log_rpow (show 0 < s+1, by linarith), exp_log],
              apply rpow_pos_of_pos,
              linarith},
            have H := s_pow_le_s_pow s s_pos hs.2,
            rw div_le_iff at H,
            apply H,
            { apply rpow_pos_of_pos,
              linarith,},
            },
          { apply rpow_pos_of_pos s_pos},
        },
      }, -- (s + 1) ^ (s + 1) / s ^ s ≤ 4
      { apply div_pos;
        { apply rpow_pos_of_pos,
          linarith},
      },
      { norm_num},
      },
      { intros Hss, -- (*)
        rw rpow_eq_zero_iff_of_nonneg (le_of_lt s_pos) at Hss,
        tauto,
      }, -- s ^ s ≠ 0
      { intros Hss, -- (**)
        rw rpow_eq_zero_iff_of_nonneg (show 0 ≤ s + 1, by linarith) at Hss,
        tauto,
      }, -- (s + 1)^(s + 1) ≠ 0
  },
end

lemma part2_2 (s : ℝ) (s_min : -1 ≤ s) (s_max : s ≤ 0): |s*log(|s|) - (s + 1) * log(|s + 1|)| ≤ 2 * log 2 :=
begin
  -- Here we go again.
  have H1 := x_log_x_le_log_two s_min s_max,
  have H2 := x_one_log_x_one_le_log_two s_min s_max,
  calc
    |s * log(|s|) - (s + 1) * log(|s + 1|)| = |s * log(|s|) + -((s + 1) * log(|s + 1|))| : by rw sub_eq_add_neg
    ... ≤  |s * log(|s|) | + | -((s + 1) * log (|s + 1|)) | : by apply abs_add
    ... = |s * log(|s|) | + | (s + 1) * log (|s + 1|) | : by rw abs_neg
    ... ≤ log 2 + log 2 : by apply add_le_add H1 H2
    ... = 2*log 2 : by linarith
end


/- OK, so I'm nearly there. I wanted to prove that (x+1)*log(x+1) - xlog x \le 2log2 
    and I could do that by proving (x+1)log(x+1) - xlog x is strict_mono-/


