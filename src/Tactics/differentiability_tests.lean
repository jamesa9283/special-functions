import .differentiablity
import analysis.special_functions.exp_log

open real

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
  {x : E}

@[differentiability] lemma differentiable_at.sin' (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sin (f x)) x := sorry

@[differentiability] lemma differentiable_at_id'' : differentiable_at ℝ (λ x, x) x :=
(has_fderiv_at_id x).differentiable_at

example {f : ℝ → ℝ} (x: ℝ) : differentiable_at ℝ (λx, real.sin (x)) x := by differentiability
