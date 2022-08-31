import computational_monads.oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

open oracle_spec

/-- Type to represent computations with access so oracles specified by and `oracle_spec` -/
inductive oracle_comp (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp α
| bind' (α β : Type) (oa : oracle_comp α) (ob : α → oracle_comp β) : oracle_comp β
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

#check vector.induction_on

-- TODO TODO: should write a more natural induction principal for `return, >>=, query`??
-- TODO: should make `return` the standard over `pure`

namespace oracle_comp

/-- Probabalistic computation is represented as access to α coin-flipping oracle -/
@[reducible, inline]
def coin : oracle_comp coin_oracle bool := oracle_comp.query () ()

section monad

/-- Natural monad structure on `oracle_comp`.
  Simplification lemmas will tend towards `pure` and `bind` over `pure'` and `bind'` -/
instance monad (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := oracle_comp.pure', bind := oracle_comp.bind' }

-- @[simp]
-- lemma pure'_eq_return (spec : oracle_spec) (a : α) :
--   (pure' α a : oracle_comp spec α) = return a := rfl

-- @[simp]
-- lemma pure_eq_return (spec : oracle_spec) (a : α) :
--   (pure a : oracle_comp spec α) = return a := rfl

@[simp]
lemma pure'_eq_pure (spec : oracle_spec) (a : α) :
  (pure' α a : oracle_comp spec α) = pure a := rfl

@[simp]
lemma return_eq_pure (spec : oracle_spec) (a : α) :
  (return a : oracle_comp spec α) = pure a := rfl

@[simp]
lemma bind'_eq_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  bind' α β oa ob = (oa >>= ob) := rfl

#check vector.induction_on


-- @[elab_as_eliminator] def induction_on (p : Π {α : Type}, oracle_comp spec α → Sort*)
--   (oa : oracle_comp spec α) (h_pure : ∀ {α : Type} (a : α), p (pure a))
--   (h_bind : ∀ {α β : Type} (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
--     (hoa : p oa) (hob : ∀ (a : α), p (ob a)), p (oa >>= ob))
--   (h_query : ∀ (i : spec.ι) (t : spec.domain i), p (query i t)) :
--   p oa :=
-- begin
--   sorry
-- end

end monad

/-- Slightly nicer induction priciple, avoiding use of `bind'` and `pure'`.
  Use as induction principle with `induction oa using oracle_comp.induction_on` -/
@[elab_as_eliminator] def induction_on {C : Π {α : Type}, oracle_comp spec α → Sort*}
  {α : Type} (oa : oracle_comp spec α)
  (h_pure : ∀ {α : Type} (a : α), C (pure a))
  (h_bind : ∀ {α β : Type} {oa : oracle_comp spec α} {ob : α → oracle_comp spec β},
    C oa → (∀ a, C (ob a)) → C (oa >>= ob) )
  (h_query : ∀ i t, C (query i t)) : C oa :=
begin
  induction oa with A a A B oa ob hoa hob i t,
  { exact h_pure _ },
  { exact h_bind hoa hob },
  { exact h_query i t }
end

/-- Check that the induction principal works properly -/
example (oa : oracle_comp spec α) : true := by induction oa using oracle_comp.induction_on; trivial

/-- Constructing an `oracle_comp` implies the existence of some element of the underlying type.
  The assumption that the range of the oracles is `inhabited` is the key point for this -/
def inhabited_base {spec : oracle_spec} :
  Π {α : Type} (oa : oracle_comp spec α), inhabited α
| _ (pure' α a) := ⟨a⟩
| _ (bind' α β oa ob) := let ⟨a⟩ := inhabited_base oa in inhabited_base (ob a)
| _ (query i t) := ⟨arbitrary (spec.range i)⟩

end oracle_comp