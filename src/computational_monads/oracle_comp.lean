import computational_monads.oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

open oracle_spec

/-- Type to represent computations with access so oracles specified by and `oracle_spec` -/
inductive oracle_comp (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp α
| bind' (α β : Type) (oa : oracle_comp α) (ob : α → oracle_comp β) : oracle_comp β
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

namespace oracle_comp

/-- Probabalistic computation is represented as access to α coin-flipping oracle -/
@[reducible, inline]
def coin : oracle_comp coin_oracle bool := oracle_comp.query () ()

section monad

/-- Natural monad structure on `oracle_comp`.
  Simplification lemmas will tend towards `pure` and `bind` over `pure'` and `bind'` -/
instance monad (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := oracle_comp.pure', bind := oracle_comp.bind' }

@[simp]
lemma pure'_eq_pure (spec : oracle_spec) (a : α) :
  (pure' α a : oracle_comp spec α) = pure a := rfl

@[simp]
lemma return_eq_pure (spec : oracle_spec) (a : α) :
  (return a : oracle_comp spec α) = pure a := rfl

@[simp]
lemma bind'_eq_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  bind' α β oa ob = (oa >>= ob) := rfl

end monad

/-- Constructing an `oracle_comp` implies the existence of some element of the underlying type.
  The assumption that the range of the oracles is `inhabited` is the key point for this -/
def inhabited_base {spec : oracle_spec} :
  Π {α : Type} (oa : oracle_comp spec α), inhabited α
| _ (pure' α a) := ⟨a⟩
| _ (bind' α β oa ob) := let ⟨a⟩ := inhabited_base oa in inhabited_base (ob a)
| _ (query i t) := ⟨arbitrary (spec.range i)⟩

end oracle_comp