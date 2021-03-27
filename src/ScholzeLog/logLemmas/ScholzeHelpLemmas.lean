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

lemma log_le_id (x : ℝ) (hx : 0 < x) : log x < x :=
begin
  -- rw ← sub_lt_zero,  
  let f := λ x, log x - x,
  have h1 : ∀ x > 0, has_deriv_at f (1/x - 1) x,
  { intros x hx,
    change f with λ x, log x - x,
    apply has_deriv_at.sub,
    { apply has_deriv_at.log,
      { apply has_deriv_at_id'},
      { linarith},
    },
    { apply has_deriv_at_id'},
  },

  sorry
end

example (x : ℝ) (hx : 0 ≤ x) : x < exp x :=
begin
  have H : 1 ≤ exp x,
  { rw [← exp_zero, exp_le_exp],
   exact hx },
  let f := λ x, exp x - x,
  have h1 : has_deriv_at f (exp x - 1) x,
  { change f with λ x, exp x - x,
    apply has_deriv_at.sub,
    { apply has_deriv_at_exp },
    { apply has_deriv_at_id' },
  },
  have h2 : 0 ≤ deriv f x,
  { rw h1.deriv,
    linarith },
  have h3 : f 0 = 0,
  { change f with λ x, exp x - x,
    simp only [exp_zero, sub_zero],
    sorry},
  have h4 : 0 ≤ f x,
  { sorry},
  have h5 : ∀ x : ℝ, 0 ≤ x → exp x - x ≤ 1,
  { sorry},
  sorry
end


example (a b : ℝ) : a < b → a - b < 0 := sub_lt_zero.mpr

private lemma dodgyScholze : 0^0 = 1 := by norm_num

lemma x_log_x_le_log_two {x : ℝ} (hx_min : -1 ≤ x) (hx_max : x ≤ 0) : |x * log(|x|)| ≤ log 2 :=
begin
  rw log_abs,
  -- have H := log_le_
  sorry
end 

example (x : ℝ) (hx_max : x < 1) (hx_min : 0 < x) : |x * log(|x|)| ≤ log 2 :=
begin
  
  sorry
end

#check rpow_le_rpow

example (x : ℝ) (hx : 0 < x) : exp(|x|) = exp x := by rw abs_of_pos hx

example (x y : ℝ) (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) : x^y ≤ 2 :=
  le_trans (rpow_le_one (le_of_lt hx) (le_of_lt hx1) (le_of_lt hy)) (show 1 ≤ (2 : ℝ), by norm_num)



lemma x_one_log_x_one_le_log_two {x : ℝ} (hx_min : -1 ≤ x) (hx_max : x ≤ 0) : |(x + 1) * log (|x + 1|)| ≤ log 2 :=
begin
  sorry
end 