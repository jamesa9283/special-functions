import .tactics .ScholzeHelpLemmas

open real set

variables {α : Type} {f : ℝ → ℝ} {s : set ℝ}

/-! # Finished-/

-- Jason's thing
lemma mono_helper (f : ℝ → ℝ) (hf : strict_mono f) : ∀ x ∈ set.Ioc (0 : ℝ) 1, 
  f x ≤ f 1 := 
begin
  rintro _ ⟨_, hx⟩,
  rcases lt_or_eq_of_le hx with h | rfl,
  { exact (le_trans $ le_of_lt $ hf h) le_rfl },
  { exact le_rfl },
end

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



/-! # Unfinished -/

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