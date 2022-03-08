import data.fintype.card
import measure_theory.probability_mass_function.constructions

/-- Specification of the various oracles available to a computation.
  `ι` index the set of oracles (e.g. `ι := ℕ` gives a different oracle for each `n : ℕ)`.
  `domain range : ι → Type` give the input and output of the oracle corresponding to `i : ι`. -/
structure oracle_comp_spec : Type 1 := 
(ι : Type)
(domain range : ι → Type)

namespace oracle_comp_spec

section instances

variables (spec : oracle_comp_spec)

/-- Class or `oracle_comp_spec` that can be computably simulated -/
class computable (spec : oracle_comp_spec) :=
(ι_decidable_eq : decidable_eq spec.ι)
(domain_decidable_eq (i : spec.ι) : decidable_eq $ spec.domain i)
(range_decidable_eq (i : spec.ι) : decidable_eq $ spec.range i)
(range_inhabited (i : spec.ι) : inhabited $ spec.range i)

instance computable.ι_decidable_eq' [spec.computable] :
  decidable_eq spec.ι := computable.ι_decidable_eq

instance computable.domain_decidable_eq' [spec.computable] (i : spec.ι) :
  decidable_eq (spec.domain i) := computable.domain_decidable_eq i

instance computable.range_decidable_eq' [spec.computable] (i : spec.ι) :
  decidable_eq (spec.range i) := computable.range_decidable_eq i

instance computable.range_inhabited' [spec.computable] (i : spec.ι) :
  inhabited (spec.range i) := computable.range_inhabited i

/-- Class of `oracle_comp_spec` for which uniform random oracles are well defined -/
class finite_range (spec : oracle_comp_spec) :=
(range_fintype (i : spec.ι) : fintype $ spec.range i)

instance finite_range.range_fintype' [spec.finite_range] (i : spec.ι) :
  fintype (spec.range i) := finite_range.range_fintype i

end instances

section empty_spec

/-- No access to any oracles -/
def empty_spec : oracle_comp_spec :=
{ ι := empty,
  domain := empty.elim,
  range := empty.elim, }

notation `[]ₒ` := empty_spec

instance empty_spec.computable : computable []ₒ := 
{ ι_decidable_eq := empty.decidable_eq,
  domain_decidable_eq := λ i, i.elim,
  range_decidable_eq := λ i, i.elim,
  range_inhabited := λ i, i.elim }

instance empty_spec.finite_range : finite_range []ₒ :=
{ range_fintype := λ i, i.elim }

instance inhabited : inhabited oracle_comp_spec := ⟨[]ₒ⟩

end empty_spec

section singleton_spec

/-- Access to a single oracle `T → U` -/
def singleton_spec (T U : Type) : oracle_comp_spec :=
{ ι := unit,
  domain := λ _, T,
  range := λ _, U, }

notation T `→ₒ` U : 67 := singleton_spec T U

variables (T U : Type)

instance singleton_spec.computable [hT : decidable_eq T] [hU' : decidable_eq U] [hU : inhabited U] :
  computable (T →ₒ U) :=
{ ι_decidable_eq := punit.decidable_eq,
  domain_decidable_eq := λ _, hT,
  range_decidable_eq := λ _, hU',
  range_inhabited := λ _, hU }

instance singleton_spec.finite_range [hU : fintype U] :
  finite_range (T →ₒ U) :=
{ range_fintype := λ _, hU }

end singleton_spec

section append

/-- Combine two specifications using a `sum` type to index the different specs -/
instance oracle_comp_spec.has_append : has_append oracle_comp_spec :=
{ append := λ spec spec', 
  { ι := spec.ι ⊕ spec'.ι,
    domain := sum.elim spec.domain spec'.domain,
    range := sum.elim spec.range spec'.range } }

variables (spec spec' : oracle_comp_spec)

instance append_computable [spec.computable] [spec'.computable] :
  computable (spec ++ spec') :=
{ ι_decidable_eq := sum.decidable_eq spec.ι spec'.ι,
  domain_decidable_eq := by refine (λ i, sum.rec_on i _ _); exact computable.domain_decidable_eq,
  range_decidable_eq := by refine (λ i, sum.rec_on i _ _); exact computable.range_decidable_eq,
  range_inhabited := by refine (λ i, sum.rec_on i _ _); exact computable.range_inhabited }

instance append_finite_range [spec.finite_range] [spec'.finite_range] :
  (spec ++ spec').finite_range :=
{ range_fintype := by refine (λ i, sum.rec_on i _ _); exact finite_range.range_fintype }

end append

section coin_oracle

@[derive [computable, finite_range]]
def coin_oracle : oracle_comp_spec := unit →ₒ bool

end coin_oracle

end oracle_comp_spec 

open oracle_comp_spec

/-- TODO: docs

Semantically, `repeat oa p` represents a procedure like: `while (a ∉ p) {a ← oa}; return a`.
Simulation semantics can be defined for this, since only one step is needed.
Probability distribution semantics are harder, since if `p` always fails there may be no output.
To solve this, let `repeatₙ oa p` be the procedure that makes at most `n` loops before stopping.
`repeat oa p` then semantically represents the limit of `repeatₙ oa p` as `n → ∞`.

Note that time-complexity semantics don't assume `repeat oa p` is polynomial time,
so it can't be used in a polynomial-time reduction, unless that is taken as an additional axiom -/
inductive oracle_comp (spec : oracle_comp_spec) : Type → Type 1
| pure' (A : Type) (a : A) : oracle_comp A
| bind' (A B : Type) (oa : oracle_comp A) (ob : A → oracle_comp B) : oracle_comp B
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)
| repeat (A : Type) (oa : oracle_comp A) (p : set A) : oracle_comp A

namespace oracle_comp

def inhabited_base {spec : oracle_comp_spec} [computable spec] :
  Π {A : Type} (oa : oracle_comp spec A), inhabited A
| _ (pure' A a) := ⟨a⟩
| _ (bind' A B oa ob) := let ⟨a⟩ := inhabited_base oa in inhabited_base (ob a)
| _ (query i t) := ⟨arbitrary (spec.range i)⟩
| _ (repeat A oa p) := inhabited_base oa

@[class]
inductive decidable {spec : oracle_comp_spec} : 
  Π {A : Type}, oracle_comp spec A → Type 1
| decidable_pure' (A : Type) (a : A) (h : decidable_eq A) : decidable (pure' A a)
| decidable_bind' (A B : Type) (oa : oracle_comp spec A) (ob : A → oracle_comp spec B)
    (hoa : decidable oa) (hob : ∀ a, decidable (ob a)) : decidable (bind' A B oa ob)
| decidable_query (i : spec.ι) (t : spec.domain i) : decidable (query i t)
| decidable_repeat (A : Type) (oa : oracle_comp spec A) (p : set A)
    (hoa : decidable oa) (hp : decidable_pred p) : decidable (repeat A oa p)

open decidable

def decidable.decidable_eq {spec : oracle_comp_spec} [computable spec] :
  Π {A : Type} {oa : oracle_comp spec A}, decidable oa → decidable_eq A
| _ _ (decidable_pure' A a h) := h
| _ _ (decidable_bind' A B oa ob hoa hob) := let ⟨a⟩ := inhabited_base oa in (hob a).decidable_eq
| _ _ (decidable_query i t) := by apply_instance
| _ _ (decidable_repeat A oa p hoa hp) := hoa.decidable_eq

def fin_support {spec : oracle_comp_spec} [spec.computable] [spec.finite_range] :
  Π {A : Type} (oa : oracle_comp spec A), decidable oa → finset A
| _ _ (decidable_pure' A a h) := {a}
| _ _ (decidable_bind' A B oa ob hoa hob) := 
  by haveI : decidable_eq B := (let ⟨a⟩ := inhabited_base oa in (hob a).decidable_eq);
  refine (fin_support oa hoa).bUnion (λ a, fin_support (ob a) (hob a))
| _ _ (decidable_query i t) := finset.univ
| _ _ (decidable_repeat A oa p hoa hp) := 
  by haveI : decidable_pred p := hp;
  refine if (∃ a ∈ (fin_support oa hoa), p a)
    then (fin_support oa hoa).filter p else (fin_support oa hoa)

private noncomputable def eval_dist {spec : oracle_comp_spec} [spec.computable] [spec.finite_range] :
  Π {A : Type} (oa : oracle_comp spec A) (hoa : decidable oa),
    Σ (pa : pmf A), plift (pa.support = oa.fin_support hoa)
| _ _ (decidable_pure' A a h) := ⟨pmf.pure a, 
  plift.up $ (pmf.support_pure a).trans (finset.coe_singleton a).symm⟩
| _ _ (decidable_bind' A B oa ob hoa hob) := 
  let pa := eval_dist oa hoa in
  let pb := λ a, eval_dist (ob a) (hob a) in
  ⟨pa.1 >>= (λ a, (pb a).1), begin
    refine plift.up _,
    refine set.ext (λ b, _),
    erw pmf.mem_support_bind_iff pa.1,
    rw fin_support,
    simp only [plift.down pa.2, finset.mem_coe, finset.mem_bUnion],
    split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩; simpa [(plift.down (pb a).2)] using ha',

  end⟩
| _ _ (decidable_query i t) := ⟨pmf.uniform_of_fintype (spec.range i),
  plift.up ((pmf.support_uniform_of_fintype (spec.range i)).trans finset.coe_univ.symm)⟩
| _ _ (decidable_repeat A oa p hoa hp) := 
  let ⟨pa, hpa⟩ := eval_dist oa hoa in
  begin
    haveI : decidable_pred p := hp,
    refine ⟨if h : ∃ a ∈ (fin_support oa hoa), p a
      then pmf.filter pa p (let ⟨a, ha, ha'⟩ := h in ⟨a, ha', (plift.down hpa).symm ▸ ha⟩) else pa, _⟩,
    refine plift.up _,
    rw fin_support,
    split_ifs,
    { simpa [plift.down hpa, set.inter_comm p] },
    { exact plift.down hpa }
  end


lemma support_eval_distribution {A : Type} (ca : oracle_comp coin_oracle A) (hca : decidable ca) :
  (eval_dist ca sorry).1.support = ca.fin_support hca :=
sorry

end oracle_comp