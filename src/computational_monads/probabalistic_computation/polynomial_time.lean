import analysis.asymptotics.superpolynomial_decay
import computability.tm_computable

import computational_monads.probabalistic_computation.oracle_base

universes u v w

section negligable

/-- `superpolynomial_decay` is a more general definition for more general spaces.
  This definition is meant to provide a cleaner API for cryptography proofs -/
def negligable {α : Type*} [topological_space α] [comm_semiring α]
  (f : ℕ → α) : Prop := 
asymptotics.superpolynomial_decay filter.at_top coe f

end negligable

section poly_time

open turing computability

/-- A function is computable in polynomial time if there is a polynomial time implementation.
  In particular this definition is extensional, so the definition of the function isn't important,
  as long as there is a Turing machine implementing the same input/output behaviour. -/
def poly_time {α β : Type} (f : α → β) :=
Σ (ea : fin_encoding α) (eb : fin_encoding β),
  tm2_computable_in_poly_time ea eb f

end poly_time

section poly_time_oracle_comp

open oracle_comp

/-- Extend polynomial time to the `oracle_comp` monad in the natural way. -/
inductive poly_time_oracle_comp {spec : oracle_comp_spec} :
  Π {α β : Type} (f : α → oracle_comp spec β), Type 1
| poly_time_pure' {α β : Type} (f : α → β) (hf : poly_time f) :
    poly_time_oracle_comp (λ a, pure' β (f a))
| poly_time_bind' {α β γ : Type} (f : α → oracle_comp spec β) (g : α → β → oracle_comp spec γ)
    (hf : poly_time_oracle_comp f) (hg : poly_time_oracle_comp (function.uncurry g)) :
    poly_time_oracle_comp (λ a, bind' β γ (f a) (g a))
| poly_time_query {α : Type} (i : spec.ι) (f : α → spec.domain i) (hf : poly_time f) :
    poly_time_oracle_comp (λ a, query i (f a))

end poly_time_oracle_comp