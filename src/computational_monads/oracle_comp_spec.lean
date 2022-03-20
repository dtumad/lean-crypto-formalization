import data.sum.basic
import data.fintype.basic

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

-- @[derive [computable]]
def uniform_selecting : oracle_comp_spec :=
{ ι := ℕ,
  domain := λ n, unit,
  range := λ n, fin (n + 1) }

instance uniform_selecting.computable : computable uniform_selecting :=
{ ι_decidable_eq := nat.decidable_eq,
  domain_decidable_eq := λ _, by apply_instance,
  range_decidable_eq := λ n, fin.decidable_eq (n + 1),
  range_inhabited := λ _, fin.inhabited }

instance uniform_selecting.finite_range : finite_range uniform_selecting :=
{ range_fintype := λ n, fin.fintype (n + 1) }

end coin_oracle

end oracle_comp_spec 