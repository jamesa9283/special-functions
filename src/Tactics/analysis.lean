import tactic differentiablity
import analysis.calculus.fderiv

namespace tactic
namespace interactive

meta def analysis : tactic unit :=
do g ← tactic.target,
  match g with
  | `(differentiable_at _ _ _) := apply_rules [``(differentiability)]
  | `(continuous_at _ _) := apply_rules [``(continuity)]
  | _ := fail "error"
  end

end interactive
end tactic

open real

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
  {x : E}

@[differentiability] lemma differentiable_at.sin' (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sin (f x)) x := sorry

@[differentiability] lemma differentiable_at_id'' : differentiable_at ℝ (λ x, x) x :=
(has_fderiv_at_id x).differentiable_at

example {f : ℝ → ℝ} (x: ℝ) : differentiable_at ℝ (λx, real.sin (x)) x := by differentiability


example 
    {𝕜 : Type*} [nondiscrete_normed_field 𝕜] 
    {E : Type*} [normed_group E] [normed_space 𝕜 E] {x : E} : differentiable_at 𝕜 id x :=
begin
  analysis, --diff
  sorry
end

example {α : Type*} [topological_space α] (x : α) : continuous_at id x :=
begin
  analysis, -- cts
  sorry
end

example : 1 + 1 = 2 :=
begin
  analysis, -- error
end