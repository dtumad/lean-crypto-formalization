import data.fintype.card
import measure_theory.probability_mass_function.constructions
import computational_monads.oracle_comp_spec

variables {A B : Type} {spec spec' : oracle_comp_spec}

open oracle_comp_spec

/-- Type to represent computations with access so oracles specified by and `oracle_comp_spec`.
  TODO: Could instead define this as a special case of a free monad -/
inductive oracle_comp (spec : oracle_comp_spec) : Type → Type 1
| pure' (A : Type) (a : A) : oracle_comp A
| bind' (A B : Type) (oa : oracle_comp A) (ob : A → oracle_comp B) : oracle_comp B
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

namespace oracle_comp

/-- Probabalistic computation is represented as access to a coin-flipping oracle -/
@[reducible, inline]
def coin : oracle_comp coin_oracle bool := oracle_comp.query () ()

section monad

/-- Natural monad structure on `oracle_comp`.
  Simplification lemmas will tend towards `pure` and `bind` over `pure'` and `bind'` -/
instance monad (spec : oracle_comp_spec) : monad (oracle_comp spec) :=
{ pure := oracle_comp.pure', bind := oracle_comp.bind' }

@[simp]
lemma pure'_eq_pure (spec : oracle_comp_spec) (a : A) :
  (pure' A a : oracle_comp spec A) = pure a := rfl

@[simp]
lemma bind'_eq_bind (ca : oracle_comp spec A) (cb : A → oracle_comp spec B) :
  bind' A B ca cb = (ca >>= cb) := rfl

end monad

/-- Constructing an `oracle_comp` implies the existence of some element of the underlying type -/
def inhabited_base {spec : oracle_comp_spec} [computable spec] :
  Π {A : Type} (oa : oracle_comp spec A), inhabited A
| _ (pure' A a) := ⟨a⟩
| _ (bind' A B oa ob) := let ⟨a⟩ := inhabited_base oa in inhabited_base (ob a)
| _ (query i t) := ⟨arbitrary (spec.range i)⟩


section support

/-- Set of possible outputs of the computation, allowing for any possible output of the queries. -/
def support {spec : oracle_comp_spec} : Π {A : Type} (oa : oracle_comp spec A), set A
| _ (pure' A a) := {a}
| _ (bind' A B ca cb) := ⋃ a ∈ ca.support, (cb a).support
| _ (query i t) := ⊤

@[simp]
lemma support_pure {A : Type} (spec : oracle_comp_spec) (a : A) :
  (pure a : oracle_comp spec A).support = {a} := rfl

lemma support_pure' {A : Type} (spec : oracle_comp_spec) (a : A) :
  (pure' A a : oracle_comp spec A).support = {a} := rfl

lemma support_return {A : Type} (spec : oracle_comp_spec) (a : A) :
  (return a : oracle_comp spec A).support = {a} := rfl

@[simp]
lemma support_bind {A B : Type} {spec : oracle_comp_spec}
  (ca : oracle_comp spec A) (cb : A → oracle_comp spec B) :
  (ca >>= cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

lemma support_bind' {A B : Type} {spec : oracle_comp_spec}
  (ca : oracle_comp spec A) (cb : A → oracle_comp spec B) :
  (bind' A B ca cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

@[simp]
lemma support_query {spec : oracle_comp_spec} (i : spec.ι) (t : spec.domain i) :
  (query i t : oracle_comp spec (spec.range i)).support = ⊤ := rfl

example : support (do {
  b ← coin, b' ← coin,
  x ← if b then return 0 else return 1,
  y ← return (if b' then 1 else 0),
  return (x * y)
} : oracle_comp coin_oracle ℕ) = {1, 0} :=
by ext x; simp

end support

@[class]
inductive decidable {spec : oracle_comp_spec} : 
  Π {A : Type}, oracle_comp spec A → Type 1
| decidable_pure' (A : Type) (a : A) (h : decidable_eq A) : decidable (pure' A a)
| decidable_bind' (A B : Type) (oa : oracle_comp spec A) (ob : A → oracle_comp spec B)
    (hoa : decidable oa) (hob : ∀ a, decidable (ob a)) : decidable (bind' A B oa ob)
| decidable_query (i : spec.ι) (t : spec.domain i) : decidable (query i t)

open decidable

def decidable.decidable_eq {spec : oracle_comp_spec} [computable spec] :
  Π {A : Type} {oa : oracle_comp spec A}, decidable oa → decidable_eq A
| _ _ (decidable_pure' A a h) := h
| _ _ (decidable_bind' A B oa ob hoa hob) := let ⟨a⟩ := inhabited_base oa in (hob a).decidable_eq
| _ _ (decidable_query i t) := by apply_instance

section fin_support

/-- Compute an explicit `finset` of the elements in `support`. -/
def fin_support {spec : oracle_comp_spec} [spec.computable] [spec.finite_range] :
  Π {A : Type} (oa : oracle_comp spec A), decidable oa → finset A
| _ _ (decidable_pure' A a h) := {a}
| _ _ (decidable_bind' A B oa ob hoa hob) := 
  by haveI : decidable_eq B := (let ⟨a⟩ := inhabited_base oa in (hob a).decidable_eq);
  refine (fin_support oa hoa).bUnion (λ a, fin_support (ob a) (hob a))
| _ _ (decidable_query i t) := finset.univ

lemma mem_fin_support_iff_mem_support {spec : oracle_comp_spec} [spec.computable] [spec.finite_range] :
  Π {A : Type} (oa : oracle_comp spec A) (hoa : decidable oa) (a : A),
    a ∈ (fin_support oa hoa) ↔ a ∈ oa.support
| _ _ (decidable_pure' A a h) a' := by simp [finset.coe_singleton a, support, fin_support]
| _ _ (decidable_bind' A B oa ob hoa hob) b := by simp [fin_support, support, mem_fin_support_iff_mem_support]
| _ _ (decidable_query i t) u := by simp [support, fin_support]

theorem coe_fin_support_eq_support {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  {A : Type} (oa : oracle_comp spec A) (hoa : decidable oa) :
    (fin_support oa hoa : set A) = oa.support :=
set.ext (mem_fin_support_iff_mem_support oa hoa)

end fin_support

end oracle_comp