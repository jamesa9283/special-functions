import data.real.basic data.nat.factorial 
import measure_theory.interval_integral
import analysis.special_functions.trigonometric
import topology.basic

open interval_integral real set
noncomputable theory


localized "notation n `!`:10000 := nat.factorial n" in nat

def Γ (n : ℕ) := (n-1)!
def G (n : ℕ) (x : ℝ) := x^(n - 1) * exp(-x)
def G' (n : ℕ) (x : ℝ) := exp(-x) * x^(n-2) * (n - 1 - x)

lemma G_def (n : ℕ) (x : ℝ) : G n x = x ^ (n - 1) * exp(-x) := rfl
lemma G'_def (n : ℕ) (x : ℝ) : G' n x = exp(-x) * x^(n-2) * (n - 1 - x) := rfl

-- the integral between 0 and ∞ of x^(z - 1) * exp(-x) = Γ (z) = (z - 1)!
def γ (n : ℕ) (a : ℝ) := ∫ x in 0..a, x^(n - 1) * exp(-x)


lemma has_deriv_at_G (x : ℝ) (n : ℕ): has_deriv_at (G n) (G' n x) x :=
begin
  rw G'_def,
  
  sorry
end


theorem integral_deriv_eq_sub'
  {E} {f' : ℝ → E} {a b : ℝ} [measurable_space E] [normed_group E]
  [topological_space.second_countable_topology E]
  [complete_space E] [normed_space ℝ E] [borel_space E]
  (f : ℝ → E)
  (hf' : deriv f = f')
  (hderiv : ∀ x ∈ interval a b, differentiable_at ℝ f x)
  (hcont' : continuous_on f' (interval a b)) :
  ∫ y in a..b, f' y = f b - f a :=
by rw [← hf', integral_deriv_eq_sub hderiv]; cc


example : ∫ x in 0..π, sin x = 2 :=
begin
  rw integral_deriv_eq_sub' (λ x, -cos x);
  norm_num,
  exact continuous_sin.continuous_on,
end


