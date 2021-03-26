import data.real.basic analysis.special_functions.exp_log
import analysis.special_functions.pow

import .tactics .BernoulliReal
open real set

notation `|`x`|` := abs x

lemma log_mul' {a b : ℝ} (hb : 0 < b) : a * log (b * a) = a * log b + a * log a :=
begin
  by_cases h: a ≠ 0,
  { rw [mul_comm b a, log_mul h, mul_add, add_comm],
    linarith},
  { rw not_not at h,
    simp only [not_not, h, zero_mul, zero_add]}
end 

lemma s_pow_le_s_pow (s : ℝ) (s_pos : 0 < s) (s_max : s ≤ 1): (s + 1) ^ (s + 1) / s ^ s ≤ 4 :=
begin
  rw rpow_add (show 0 < s +1, by linarith),
  rw rpow_one,
  rw ← div_mul_eq_mul_div,
  rw ← div_rpow (show 0 ≤ s +1, by linarith) (le_of_lt s_pos),
  rw add_div,
  rw div_self (show s ≠ 0, by linarith),
  have H1 : 0 < 1/s, {rw one_div_pos, exact s_pos},
  have HT : (1 + 1/s)^s * (s + 1) ≤ 2 * (s+1),
  { apply mul_le_mul,
    { rw ← one_add_one_eq_two,
      conv_rhs {
        congr,
        skip,
        rw ← div_self (show s ≠ 0, by linarith), 
        rw ← mul_one_div,
      },
      -- rw ← [one_add_one_eq_two, div_self , mul_one_div],
      apply BernoulliInequality (1/s) (le_of_lt H1) s (le_of_lt s_pos) s_max,},
    { refl},
    { linarith,},
    { norm_num},
  },
  have HTw : (s + 1) ≤ 2,
  { linarith,},
  linarith,
end

lemma x_log_x_le_log_two {x : ℝ} (hx_min : -1 ≤ x) (hx_max : x ≤ 0) : |x * log(|x|)| ≤ log 2 :=
begin
  sorry
end 

lemma x_one_log_x_one_le_log_two {x : ℝ} (hx_min : -1 ≤ x) (hx_max : x ≤ 0) : |(x + 1) * log (|x + 1|)| ≤ log 2 :=
begin
  sorry
end 