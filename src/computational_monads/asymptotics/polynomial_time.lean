/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.poly_time
import computational_monads.distribution_semantics.equiv
/-!
# Polynomial Time Complexity of Oracle Computations

This file extends the definition `poly_time` from functions `α → β`
to functions `α → oracle_comp spec β` for some `spec : oracle_spec`.
The definition is inductive, constructed by proving each step of the computation
is itself polynomial time.
-/

namespace oracle_comp

/-- Extend polynomial time to the `oracle_comp` monad in the natural way. -/
inductive poly_time_oracle_comp {spec : oracle_spec} :
  Π {α β : Type} (f : α → oracle_comp spec β), Type 1
| poly_time_pure' {α β : Type} (f : α → β) (hf : poly_time f) :
    poly_time_oracle_comp (λ a, pure' β (f a))
| poly_time_bind' {α β γ : Type} (f : α → oracle_comp spec β) (g : α → β → oracle_comp spec γ)
    (hf : poly_time_oracle_comp f) (hg : poly_time_oracle_comp (function.uncurry g)) :
    poly_time_oracle_comp (λ a, bind' β γ (f a) (g a))
| poly_time_query {α : Type} (i : spec.ι) (f : α → spec.domain i) (hf : poly_time f) :
    poly_time_oracle_comp (λ a, query i (f a))
-- For distributions, suffices to show there is a poly time implementation
| poly_time_ext [spec.finite_range] [spec.computable]
    {α β : Type} (f g : α → oracle_comp spec β)
    (h : ∀ a, f a ≃ₚ g a) (hf : poly_time_oracle_comp g) :
    poly_time_oracle_comp f

end oracle_comp