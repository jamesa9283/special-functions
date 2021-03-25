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
      all_goals{linarith [x_pos]
      }, -- need to add 0 < x
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