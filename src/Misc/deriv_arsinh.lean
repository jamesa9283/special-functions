import analysis.special_functions.arsinh
import data.real.sqrt

open real

--lemma arsinh_def : arsinh  = log (x + sqrt (1 + x^2)) := rfl

--lemma diff_arsinh (x : ℝ) : deriv (λ y, real.asinh y) x = 1/real.sqrt( 1 + x^2 ) := sorry




lemma la_reduc (x : ℝ) (f : ℝ → ℝ) : deriv (λ y, f y) x = deriv f x := rfl

example (x : ℝ) : has_deriv_at arsinh ( 1 / real.sqrt( 1 + x^2 ) ) x :=
begin
  rw has_deriv_at_iff_is_o_nhds_zero,
  have : (1 : ℕ) < 2 := by norm_num,
  refine (asymptotics.is_O.of_bound (∥1 / real.sqrt( 1 + x^2) ∥) _).trans_is_o (asymptotics.is_o_pow_id this),
  filter_upwards [metric.ball_mem_nhds (0 : ℝ) zero_lt_one],
  simp only [metric.mem_ball, dist_zero_right, normed_field.norm_pow],
  intros h Hh,
  /-
  x : ℝ,
  this : 1 < 2,
  h : ℝ,
  Hh : ∥h∥ < 1
  ⊢ ∥arsinh (x + h) - arsinh x - h • (1 / sqrt (1 + x ^ 2))∥ ≤ ∥1 / sqrt (1 + x ^ 2)∥ * ∥h∥ ^ 2
  -/
  unfold arsinh,
  rw sub_eq_add_neg _ (log (x + sqrt (1 + x ^ 2))),
  rw ← log_inv (x + sqrt (1 + x ^ 2)),
  rw ← log_mul,
  { ring,
    sorry
  },
  { 
    sorry
  },
  { sorry}
end

example (a b : ℝ) : a - b = a + -b := sub_eq_add_neg a b


example (x : ℝ) (h : 0 ≤ x) : real.sqrt x = x^(1/2) :=
begin
  have H := mul_self_sqrt h,

  sorry
end