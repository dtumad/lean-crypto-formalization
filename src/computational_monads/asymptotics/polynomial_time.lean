import analysis.asymptotics.superpolynomial_decay
import computability.tm_computable

import computational_monads.oracle_comp
import computational_monads.distribution_semantics.equiv
import computational_monads.simulation_semantics.simulate

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

noncomputable lemma poly_time_id (α : Type) (ea : fin_encoding α) : poly_time (id : α → α) :=
⟨ea, ea, id_computable_in_poly_time ea⟩

end poly_time

section poly_time_oracle_comp

open oracle_comp

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
| poly_time_ext [spec.finite_range] [spec.computable]
    {α β : Type} (f g : α → oracle_comp spec β)
    (h : ∀ a, f a ≃ₚ g a) (hf : poly_time_oracle_comp g) :
    poly_time_oracle_comp f

open poly_time_oracle_comp

-- /-- Simulating something polynomial time with polynomial time oracles is still polynomial time-/
-- theorem poly_time_simulate {spec spec' : oracle_spec} {α β : Type}
--   (so : simulation_oracle spec spec') (s : so.S)
--   (hso : ∀ (i : spec.ι), poly_time_oracle_comp $ so.o i) :
--   Π (f : α → oracle_comp spec β) (hf : poly_time_oracle_comp f),
--   poly_time_oracle_comp (λ a, simulate so (f a) s) :=
-- begin
--   sorry
-- end

end poly_time_oracle_comp