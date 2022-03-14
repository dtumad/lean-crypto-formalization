import computational_monads.probabalistic_computation.oracle_base

namespace oracle_comp 

open oracle_comp_spec

def inhabited_base {spec : oracle_comp_spec} [computable spec] :
  Π {A : Type} (oa : oracle_comp spec A), inhabited A
| _ (pure' A a) := ⟨a⟩
| _ (bind' A B oa ob) := let ⟨a⟩ := inhabited_base oa in inhabited_base (ob a)
| _ (query i t) := ⟨arbitrary (spec.range i)⟩

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