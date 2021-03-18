import data.real.basic analysis.special_functions.exp_log
import analysis.special_functions.pow

import tactic

/- In this file we prove Schloze Lemma 5.3 from https://www.math.uni-bonn.de/people/scholze/Analytic.pdf -/

notation `|`x`|` := abs x

open real set

meta def diff : tactic unit :=
`[apply_rules [differentiable_at_id,
               differentiable_at.log,
               differentiable_at.const_add, 
               differentiable_at.add_const, 
               differentiable_at.const_mul, 
               differentiable_at.const_sub,
               differentiable_at.mul
               ], 
               all_goals{linarith}]

meta def cont_on : tactic unit :=
`[apply_rules [continuous_on_id,
               continuous_on.log,
               continuous_on.mul,
               continuous_on.add
               ]]

-- Right so I now need to prove that it's differentiable
lemma diff_helper (s : ℝ) (s_pos : 0 < s) : deriv (λ x, (x + 1) * log(x + 1) - x*log x) s = log(s+1) - log(s) :=
begin
  simp {discharger:= `[diff]},
  rw deriv.comp,
  simp only [add_zero, differentiable_at_const, mul_one, one_mul, differentiable_at_id', deriv_id'', deriv_log', deriv_const',
  deriv_add],
  rw [mul_inv_cancel, mul_inv_cancel];
  linarith,
  all_goals{diff},
end

-- Jason's thing
lemma mono_helper (f : ℝ → ℝ) (hf : strict_mono f) : ∀ x ∈ set.Ioc (0 : ℝ) 1, 
  f x ≤ f 1 := 
begin
  rintro _ ⟨_, hx⟩,
  rcases lt_or_eq_of_le hx with h | rfl,
  { exact (le_trans $ le_of_lt $ hf h) le_rfl },
  { exact le_rfl },
end

lemma log_mul' {a b : ℝ} (hb : 0 < b) : a * log (b * a) = a * log b + a * log a :=
begin
  by_cases h: a ≠ 0,
  { rw [mul_comm b a, log_mul h, mul_add, add_comm],
    linarith},
  { rw not_not at h,
    simp only [not_not, h, zero_mul, zero_add]}
end 

lemma part1 (s t l : ℝ) (hl : 0 < l) : |l*s*log (|l * s|) + l*t*log(|l*t|) - (l*s + l*t)*log(|l*s + l*t|)| 
    = l * |s*log(|s|) + t*log(|t|) - (s + t)*log(|s + t|)| :=
begin
  conv_rhs { rw [← abs_of_pos hl, ← abs_mul]},
  congr',
  simp only [log_mul', ← mul_add, mul_assoc, log_mul' hl, log_abs],
  ring,
end

variables {α : Type} {f : ℝ → ℝ} {s : set ℝ}

lemma continuous_on.id_log (hf : continuous_on f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
  continuous_on (λ x, x * log (f x)) s :=
--λ x hx, (hf x hx).log (h₀ x hx)
begin
  intros x hx,
  apply continuous_within_at.mul,
  { apply continuous_within_at_id},
  { apply continuous_within_at.log,
    { exact hf x hx,},
    { exact h₀ x hx},
  },
end

-- example (s t a : ℝ) (hst : s < t) (ha : -1 < a ∧ a < 1) : s = a * t := by library_search

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


lemma log_stuff_pos (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) (s_pos : 0 < s): |s*log(|s|) - (s + 1) * log(|s + 1|)| ≤ 2 * log 2 :=
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
            { 
              sorry
            },

            sorry},
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

lemma x_log_x_cont : continuous_on (λ x, (x + 1) * log (x + 1) - x * log x) (Icc 0 1) :=
begin
  apply continuous_on.add,
  { apply continuous_on.mul,
    { apply continuous_on.add,
      { apply continuous_on_id},
      { apply continuous_on_const},
    },
    { apply continuous_on.log,
      { apply continuous_on.add,
        { apply continuous_on_id},
        { apply continuous_on_const},
      },
      { intros x x_in,
        rw [← Icc_def, mem_set_of_eq] at x_in,
        linarith,},
    },
  },
  { -- prove the xlog x is continuous.
    apply continuous_on.neg,
    apply continuous_on.id_log,
    { apply continuous_on_id,},
    { -- needs me to prove that ∀ x ∈ Icc 0 1, x ≠ 0
      sorry},
  }
end

example (s : ℝ) (s_pos : 0 < s) (s_max : s ≤ 1): (s + 1) ^ (s + 1) / s ^ s ≤ 4 :=
begin
  rw div_le_iff,
  have pow_to_exp1 : 4*s^s = exp(log 4 + s*log s),
    { rw [exp_add, exp_log (show 0 < (4 : ℝ), by norm_num), ← log_rpow s_pos, exp_log],
      apply rpow_pos_of_pos,
      linarith},
  have pow_to_exp2 : (s+1)^(s+1) = exp((s+1) * log(s+1)),
    { rw [← log_rpow (show 0 < s + 1, by linarith), exp_log],
      apply rpow_pos_of_pos,
      linarith},
  { rw [pow_to_exp1, pow_to_exp2],
    rw exp_le_exp,
    have H1 : ∀ {x : ℝ}, 0 < x → 0 < deriv (λ (x : ℝ), (x + 1) * log (x + 1) - x * log x) x,
    { intros x x_pos, 
      rw diff_helper,
      rw ← log_div,
      apply log_pos,
      rw one_lt_div,
      linarith,
      all_goals{linarith [x_pos]} -- need to add 0 < x
    },
    have H := convex.strict_mono_of_deriv_pos (convex_Icc 0 1) x_log_x_cont _ _,
    { sorry},
    { apply differentiable_on.sub,
      { apply differentiable_on.mul,
        { apply differentiable_on.add_const differentiable_on_id,},
        { apply differentiable_on.log,
          { apply differentiable_on.add_const differentiable_on_id,},
          { intros x hx, 
            rw mem_interior at *,
            -- screams
            sorry},
        },
      },
      { sorry},
    },
    { -- ∀ (x : ℝ), x ∈ interior (Icc 0 1) → 0 < deriv (λ (x : ℝ), (x + 1) * log (x + 1) - x * log x) x
      sorry},
    
    all_goals{sorry} -- (s + 1) * log (s + 1) ≤ log 4 + s * log s
  },
  { apply rpow_pos_of_pos,
    linarith}
end

#check continuous_on (λ x, (x + 1) * log (x + 1) - x * log x) (Icc 0 1)


example (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1): |s*log(|s|) - (s + 1) * log(|s + 1|)| ≤ 2 * log 2 :=
begin
  -- PAIN
  -- This proof isn't that bad. I want to provide an argument relating to the fact that log is 
  -- monotonically increasing on s ∈ [0, 1]. The question now, is how?
    -- OK. So now I had an idea about using log x < log y → x < y, but it's a sum of logs.
  by_cases s_pos: 0 < s,
  { apply log_stuff_pos s hs s_pos,
  },
  { rw [not_lt] at s_pos,
    -- log time! Right I need to prove the other side now.
    --
    
    sorry
  }
end

-- example (a s : ℝ) : a*s^s = s^(log a + s) := by library_search

example (a x : ℝ) (hx : 0 < x) : a * log x = log (x ^ a) := (log_rpow hx a).symm

-- example (a : ℝ) : a ^ (2 : ℝ) = a * a := by library_search

-- example (a b c : ℝ) (h : a / b < c) : a < b * c := by library_search

example (a b c d e : ℝ) : a * b * c + a * d * e = a * (b * c + d * e) := by ring