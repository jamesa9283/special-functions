import tactic

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