import data.fintype.basic

/-- Specification of the various oracles available to a computation.
  `ι` index the set of oracles (e.g. `ι := ℕ` gives a different oracle for each `n : ℕ)`.
  `domain range : ι → Type` give the input and output of the oracle corresponding to `i : ι`. -/
structure oracle_spec : Type 1 := 
(ι : Type)
(domain range : ι → Type)
(range_inhabited (i : ι) : inhabited $ range i)

/-- Example of a simple `oracle_spec` for a pair of oracles,
  each taking a `ℕ` as input, returning a value of type `ℕ` or `ℤ` respectively -/
example : oracle_spec :=
{ ι := unit ⊕ unit,
  domain := λ _, ℕ,
  range := λ x, match x with | (sum.inl ()) := ℕ | (sum.inr ()) := ℤ end,
  range_inhabited := λ x, match x with
  | (sum.inl ()) := nat.inhabited
  | (sum.inr ()) := int.inhabited
  end }

namespace oracle_spec

section instances

@[simp]
instance range_inhabited' {spec : oracle_spec} (i : spec.ι) : inhabited (spec.range i) :=
spec.range_inhabited i

variables (spec : oracle_spec)

/-- Class of `oracle_spec` that have decidable equality on the underlying types.
This is needed for things like cacheing previous queries or checking for specific queries.
It also allows for explicit calculation of the support of the computation (see `fin_support`)
We choose the name `computable` to avoid confusion with `oracle_comp.decidable` -/
class computable (spec : oracle_spec) :=
(ι_decidable_eq : decidable_eq spec.ι)
(domain_decidable_eq (i : spec.ι) : decidable_eq $ spec.domain i)
(range_decidable_eq (i : spec.ι) : decidable_eq $ spec.range i)

instance computable.ι_decidable_eq' [spec.computable] :
  decidable_eq spec.ι := computable.ι_decidable_eq

instance computable.domain_decidable_eq' [spec.computable] (i : spec.ι) :
  decidable_eq (spec.domain i) := computable.domain_decidable_eq i

instance computable.range_decidable_eq' [spec.computable] (i : spec.ι) :
  decidable_eq (spec.range i) := computable.range_decidable_eq i

/-- Class of `oracle_spec` for which uniform random oracles are well defined -/
class finite_range (spec : oracle_spec) :=
(range_fintype (i : spec.ι) : fintype $ spec.range i)

instance finite_range.range_fintype' [spec.finite_range] (i : spec.ι) :
  fintype (spec.range i) := finite_range.range_fintype i

end instances

section empty_spec
 
/-- No access to any oracles -/
def empty_spec : oracle_spec :=
{ ι := empty,
  domain := empty.elim,
  range := λ _, unit,
  range_inhabited := λ _, by apply_instance }

notation `[]ₒ` := empty_spec

instance empty_spec.computable : computable []ₒ := 
{ ι_decidable_eq := empty.decidable_eq,
  domain_decidable_eq := λ i, i.elim,
  range_decidable_eq := λ i, i.elim }

instance empty_spec.finite_range : finite_range []ₒ :=
{ range_fintype := λ i, i.elim }

instance inhabited : inhabited oracle_spec := ⟨[]ₒ⟩

end empty_spec

section singleton_spec

/-- Access to a single oracle `T → U` -/
def singleton_spec (T U : Type) [hU : inhabited U] : oracle_spec :=
{ ι := unit,
  domain := λ _, T,
  range := λ _, U,
  range_inhabited := λ _, hU }

infixl` ↦ₒ `:25 := singleton_spec

variables (T U : Type) [inhabited U]

instance singleton_spec.computable [hT : decidable_eq T] [hU' : decidable_eq U] :
  computable (T ↦ₒ U) :=
{ ι_decidable_eq := punit.decidable_eq,
  domain_decidable_eq := λ _, hT,
  range_decidable_eq := λ _, hU' }

instance singleton_spec.finite_range [hU : fintype U] :
  finite_range (T ↦ₒ U) :=
{ range_fintype := λ _, hU }

end singleton_spec

section append

/-- Combine two specifications using a `sum` type to index the different specs -/
instance oracle_spec.has_append : has_append oracle_spec :=
{ append := λ spec spec', 
  { ι := spec.ι ⊕ spec'.ι,
    domain := sum.elim spec.domain spec'.domain,
    range := sum.elim spec.range spec'.range,
    range_inhabited := λ i, by induction i; simp; apply_instance } }

variables (spec spec' : oracle_spec)

instance append_computable [spec.computable] [spec'.computable] :
  computable (spec ++ spec') :=
{ ι_decidable_eq := sum.decidable_eq spec.ι spec'.ι,
  domain_decidable_eq := by refine (λ i, sum.rec_on i _ _); exact computable.domain_decidable_eq,
  range_decidable_eq := by refine (λ i, sum.rec_on i _ _); exact computable.range_decidable_eq }

instance append_finite_range [spec.finite_range] [spec'.finite_range] :
  (spec ++ spec').finite_range :=
{ range_fintype := by refine (λ i, sum.rec_on i _ _); exact finite_range.range_fintype }

end append

section coin_oracle

@[derive [finite_range, computable]]
def coin_oracle : oracle_spec := unit ↦ₒ bool

@[simp] lemma coin_oracle.range.card : fintype.card (coin_oracle.range ()) = 2 := rfl

end coin_oracle

section uniform_selecting

def uniform_selecting : oracle_spec :=
{ ι := ℕ,
  domain := λ n, unit,
  range := λ n, fin (n + 1),
  range_inhabited := λ n, by apply_instance }

instance uniform_selecting.computable : computable uniform_selecting :=
{ ι_decidable_eq := nat.decidable_eq,
  domain_decidable_eq := λ _, by apply_instance,
  range_decidable_eq := λ n, fin.decidable_eq (n + 1) }

instance uniform_selecting.finite_range : finite_range uniform_selecting :=
{ range_fintype := λ n, fin.fintype (n + 1) }

@[simp]
lemma uniform_selecting.domain_apply (n : ℕ) :
  uniform_selecting.domain n = unit :=
rfl

@[simp]
lemma uniform_selecting.range_apply (n : ℕ) :
  uniform_selecting.range n = fin (n + 1) :=
rfl

end uniform_selecting

end oracle_spec 