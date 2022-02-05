import to_mathlib
import measure_theory.probability_mass_function.constructions

open_locale classical big_operators nnreal ennreal

variables {A B : Type} (a a' : A) (b : B)

/-- computational monad to extend the base language of Lean for modeling cryptographic algorithms.
  Note that because Lean doesn't have an impredicative base type, this raises universe levels.
  `uniform bag` represents uniformly randomly sampling an element of the finite set `bag`.
  `bind ca cb` represents running `ca`, passing the result to `cb`, and running the result.
  `repeat p ca` represents running `ca` until the output satisfies `p` -/
inductive prob_alg : Π (A : Type), Type 1
| uniform {A : Type} (bag : finset A) : prob_alg A
| bind' (A B : Type) (ca : prob_alg A) (cb : A → prob_alg B) : prob_alg B
| repeat {A : Type} (ca : prob_alg A) (p : A → Prop) : prob_alg A

namespace prob_alg

variables (ca ca' : prob_alg A) (cb : A → prob_alg B)
  (bag : finset A) (p : A → Prop)

section monad

/-- Create a monad structure, using uniform sampling from a singleton set as `return` -/
@[simps]
instance monad : monad prob_alg :=
{ pure := λ A a, uniform {a},
  bind := bind' }

@[simp] lemma return_eq_uniform_singleton :
  (return a : prob_alg A) = uniform {a} := rfl

@[simp] lemma bind_eq_bind' :
  ca >>= cb = bind' A B ca cb := rfl

end monad

/-- Example of a computation computing the sum of a random odd element and random even element -/
example : prob_alg ℕ :=
let nums : finset ℕ := {1, 2, 3, 4, 5} in do { 
  x ← (prob_alg.uniform nums).repeat odd,
  y ← (prob_alg.uniform nums).repeat even,
  return (x + y)
}

section support

/-- The support of `ca : prob_comp A` is the set outputs in `A` with non-zero probability -/
def support : Π {A : Type}, prob_alg A → set A
| A (uniform bag) := ↑bag
| _ (bind' A B ca cb) := ⋃ a ∈ ca.support, (cb a).support
| A (repeat ca p) := {a ∈ ca.support | p a}

@[simp] lemma support_uniform :
  (uniform bag).support = ↑bag := rfl

lemma mem_support_uniform_iff :
  a ∈ (uniform bag).support ↔ a ∈ bag := iff.rfl

lemma support_return :
  support (return a) = ({a} : finset A) := support_uniform {a}

lemma mem_support_return_iff (a' : A) :
  a ∈ support (return a') ↔ a = a':= by simp

@[simp] lemma support_bind' :
  (bind' A B ca cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

lemma mem_support_bind'_iff : 
  b ∈ (bind' A B ca cb).support ↔ ∃ a ∈ ca.support, b ∈ (cb a).support := by simp

lemma support_bind :
  (ca >>= cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

lemma mem_support_bind_iff :
  b ∈ (ca >>= cb).support ↔ ∃ a ∈ ca.support, b ∈ (cb a).support := by simp

@[simp] lemma support_repeat :
  (ca.repeat p).support = {a ∈ ca.support | p a} := rfl

lemma mem_support_repeat_iff :
  a ∈ (ca.repeat p).support ↔ a ∈ ca.support ∧ p a := iff.rfl

end support

section well_formed

/-- `well_formed ca` says that `ca` has at least one possible output, needed to define evalutaion.
  In particular, for any `uniform bag` step `bag` must be nonempty,
  and for each `repeat p ca` there must be some output of `ca` satisfying `p` -/
def well_formed : Π {A : Type}, prob_alg A → Prop
| A (uniform bag) := bag.nonempty
| _ (bind' A B ca cb) := ca.well_formed ∧ ∀ a ∈ ca.support, (cb a).well_formed
| A (repeat ca p) := ca.well_formed ∧ ∃ a ∈ ca.support, p a

/-- The `well_formed` predicate is equivalent to having nonempty support -/
lemma support_nonempty_of_well_formed :
  Π {A : Type} (ca : prob_alg A), ca.well_formed → ca.support.nonempty
| A (uniform bag) uniform_wf := uniform_wf
| _ (bind' A B ca cb) bind_wf := 
    let ⟨ca_wf, cb_wf⟩ := bind_wf in
    let ⟨a, ha⟩ := support_nonempty_of_well_formed ca ca_wf in
    let ⟨b, hb⟩ := support_nonempty_of_well_formed (cb a) (cb_wf a ha) in
    set.nonempty_Union.2 ⟨a, set.nonempty_Union.2 ⟨ha, ⟨b, hb⟩⟩⟩
| A (repeat ca p) repeat_wf := let ⟨ca_wf, ⟨a, ha, hpa⟩⟩ := repeat_wf in ⟨a, ⟨ha, hpa⟩⟩

@[simp] lemma uniform_well_formed_iff :
  (uniform bag).well_formed ↔ bag.nonempty := iff.rfl

lemma uniform_well_formed {bag : finset A} (hbag : bag.nonempty) :
  (uniform bag).well_formed := hbag

lemma uniform_singleton_well_formed (a : A) :
  (uniform ({a} : finset A)).well_formed := uniform_well_formed (finset.singleton_nonempty a)

lemma uniform_insert_well_formed [decidable_eq A] (bag : finset A) (a : A) :
  (uniform (insert a bag)).well_formed := 
uniform_well_formed (finset.insert_nonempty a bag)

lemma nonempty_of_uniform_well_formed : (uniform bag).well_formed → bag.nonempty
| h := h

@[simp] lemma return_well_formed :
  (return a : prob_alg A).well_formed := by exact ⟨a, finset.mem_singleton_self a⟩

@[simp] lemma bind'_well_formed_iff :
  (bind' A B ca cb).well_formed ↔ ca.well_formed ∧ ∀ a ∈ ca.support, (cb a).well_formed := iff.rfl

lemma bind'_well_formed {ca : prob_alg A} {cb : A → prob_alg B}
  (hca : ca.well_formed) (hcb : ∀ a ∈ ca.support, (cb a).well_formed) :
  (bind' A B ca cb).well_formed := ⟨hca, hcb⟩

@[simp] lemma bind_well_formed_iff :
  (ca >>= cb).well_formed ↔ ca.well_formed ∧ ∀ a ∈ ca.support, (cb a).well_formed := iff.rfl

lemma bind_well_formed {ca : prob_alg A} {cb : A → prob_alg B}
  (hca : ca.well_formed) (hcb : ∀ a ∈ ca.support, (cb a).well_formed) :
  (ca >>= cb).well_formed := ⟨hca, hcb⟩

@[simp] lemma repeat_well_formed_iff :
  (repeat ca p).well_formed ↔ ca.well_formed ∧ ∃ a ∈ ca.support, p a := iff.rfl

lemma repeat_well_formed {ca : prob_alg A} {p : A → Prop}
  (hca : ca.well_formed) (hp : ∃ a ∈ ca.support, p a) :
  (repeat ca p).well_formed := ⟨hca, hp⟩

lemma well_formed_of_repeat_well_formed : (repeat ca p).well_formed → well_formed ca
| h := h.1

example (z : ℕ) : well_formed 
  (do x ← return (z + 3),
      y ← return (x * z), 
      return (x + y + z)) := by simp

end well_formed

end prob_alg

-------------------------------------------------

structure prob_comp (A : Type) :=
(alg : prob_alg A)
(wf : alg.well_formed)

namespace prob_comp

variables (ca : prob_comp A) (cb : A → prob_comp B)

section eval_distribution

/-- Private definition used to bootstrap the actual evalution function.
  The reason this is to equate the `pmf` supports with the `prob_comp` supports
  TODO: Maybe this should return an option, and not require well_formed -/
private noncomputable def eval_distribution' :
  Π {A : Type} (ca : prob_alg A) (hca : ca.well_formed), 
    Σ (pa : pmf A), plift (∀ (a : A), (a ∈ pa.support ↔ a ∈ ca.support))
| A (prob_alg.uniform bag) uniform_wf :=
  ⟨pmf.uniform_of_finset bag uniform_wf,
    plift.up $ pmf.mem_support_uniform_of_finset_iff uniform_wf⟩
| _ (prob_alg.bind' A B ca cb) bind_wf :=
  let pa := eval_distribution' ca bind_wf.1 in
  let pb := λ a ha, eval_distribution' (cb a) (bind_wf.2 a ha) in
  ⟨pa.1.bind_on_support $ λ a ha, (pb a $ ((plift.down pa.2) a).1 ha).1,
    plift.up $ λ b, begin
      simp only [pmf.mem_support_bind_on_support_iff, prob_alg.mem_support_bind'_iff, plift.down pa.2],
      split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩; simpa [(plift.down (pb a ha).2) b] using ha'
    end⟩
| A (prob_alg.repeat ca p) repeat_wf :=
  let ⟨ca_wf, hp⟩ := repeat_wf in
  let ⟨pa, hpa⟩ := eval_distribution' ca ca_wf in
  ⟨pa.filter p (let ⟨a, ha, hap⟩ := hp in ⟨a, hap, (plift.down hpa a).2 ha⟩),
    plift.up $ λ a, (pmf.mem_support_filter_iff _ a).trans
      (by rw [plift.down hpa a]; exact and_comm (p a) (a ∈ ca.support))⟩

/-- Denotational semantics for evaluation of a `prob_comp A`, as a probability distribution.
  The distribution is given by a probability mass function `pmf A` on the underlying type.
  This requires providing a proof of well formedness to ensure the distribution sums to `1`.-/
noncomputable def eval_distribution (ca : prob_comp A) : pmf A :=
(eval_distribution' ca.alg ca.wf).1

@[simp]
theorem support_eval_distribution_eq_support (ca : prob_comp A) :
  (eval_distribution ca).support = ca.alg.support :=
set.ext (plift.down (eval_distribution' ca.alg ca.wf).snd)

end eval_distribution

section prob_event

/-- The probability of an event holding on the result of a probablistic computation.
  The definition is in terms of the `outer_measure` structure induced by the `eval_distribution`.
  This is equivalent to the sum of the probabilities of each element of the set. -/
noncomputable def prob_event (ca : prob_comp A) (event : set A) : ennreal :=
ca.eval_distribution.to_outer_measure event

end prob_event

section monad 

instance monad : monad prob_comp :=
{ pure := λ A a, ⟨return a, prob_alg.return_well_formed a⟩,
  bind := λ A B ca cb, ⟨ca.alg >>= (alg ∘ cb),
    prob_alg.bind_well_formed ca.wf (λ a _, (cb a).wf)⟩ }

@[simp] lemma alg_return : alg (return a) = return a := rfl

@[simp] lemma alg_bind : alg (ca >>= cb) = (alg ca) >>= (alg ∘ cb) := rfl

@[simp]
lemma eval_distribution_return_eq_pure : eval_distribution (return a) = pmf.pure a :=
begin
  show pmf.uniform_of_finset {a} _ = pmf.pure a,
  refine pmf.ext (λ a, by simp)
end

@[simp]
lemma eval_distribution_return_apply :
  eval_distribution (return a') a = if a = a' then 1 else 0 := by simp

@[simp]
lemma eval_distribution_return_apply_self :
  eval_distribution (return a) a = 1 := by simp

@[simp]
lemma eval_distribution_bind_eq_bind :
  eval_distribution (ca >>= cb) = (eval_distribution ca) >>= (eval_distribution ∘ cb) :=
sorry

end monad

section uniform

@[simps]
def uniform (bag : finset A) (h : bag.nonempty) : prob_comp A :=
⟨prob_alg.uniform bag, prob_alg.uniform_well_formed h⟩

@[simp]
lemma eval_distribution_uniform_eq_uniform_of_finset (bag : finset A) (h : bag.nonempty) :
  eval_distribution (uniform bag h) = pmf.uniform_of_finset bag h := rfl

lemma eval_distribution_uniform_apply (bag : finset A) (h : bag.nonempty) :
  eval_distribution (uniform bag h) a = if a ∈ bag then (bag.card : ℝ≥0)⁻¹ else 0 :=
by exact pmf.uniform_of_finset_apply h a


end uniform

section repeat

@[simps]
def repeat (ca : prob_comp A) (p : A → Prop) (hp : ∃ a ∈ ca.alg.support, p a) : prob_comp A :=
⟨ca.alg.repeat p, prob_alg.repeat_well_formed ca.wf hp⟩

end repeat

section prod

def prod (ca : prob_comp A) (cb : prob_comp B) :
  prob_comp (A × B) :=
do { a ← ca, b ← cb, return (a, b) }

infix ` ×× `:80 := prod

lemma support_prod (ca : prob_comp A) (cb : prob_comp B) :
  (ca ×× cb).alg.support = ⋃ (a ∈ ca.alg.support) (b ∈ cb.alg.support), {(a, b)} :=
by simp [prod]

end prod

end prob_comp

--------------------------------------------------------

structure oracle_comp_spec :=
(ι : Type)
(D R : ι → Type)

namespace oracle_comp_spec

def domain (spec : oracle_comp_spec)
  (i : spec.ι) : Type :=
spec.D i

def range (spec : oracle_comp_spec)
  (i : spec.ι) : Type :=
spec.R i

/-- No access to any oracles -/
def empty_spec : oracle_comp_spec :=
{ ι := empty,
  D := empty.elim,
  R := empty.elim }

/-- Access to a single oracle `A → B` -/
def singleton_spec (A B : Type) : oracle_comp_spec :=
{ ι := unit,
  D := λ _, A,
  R := λ _, B }

alias singleton_spec ← oracle_comp_spec.random_oracle_spec

@[reducible]
instance has_append : has_append oracle_comp_spec :=
{ append := λ spec spec', 
  { ι := spec.ι ⊕ spec'.ι,
    D := sum.elim spec.D spec'.D,
    R := sum.elim spec.R spec'.R } } 

end oracle_comp_spec 

open oracle_comp_spec

/-- `oracle_comp A B C` is the type of a computation of a value of type `C`,
  with access to a family of oracle taking values in `A t` to values in `B t`.
  The oracle's semantics aren't specified until evaluation (`eval_distribution`),
    since algorithm specification only needs to know the types, not the values.
  Requiring well formed in the constructor avoids
  
TODO: ret → sample, bind → bind' -/
inductive oracle_comp (spec : oracle_comp_spec) : Type → Type 1
| oc_ret {C : Type} (c : prob_comp C) : oracle_comp C
| oc_bind {C D : Type} (oc : oracle_comp C) (od : C → oracle_comp D) : oracle_comp D
| oc_query (i : spec.ι) (a : spec.domain i) : oracle_comp (spec.range i)

namespace oracle_comp

@[simps]
instance monad (spec : oracle_comp_spec) :
  monad (oracle_comp spec) :=
{ pure := λ C c, oracle_comp.oc_ret (return c),
  bind := λ C D, oracle_comp.oc_bind }

-- Example of accessing a pair of different oracles and passing
example (α β A B : Type) (ca : prob_comp α) (cb : prob_comp β) : 
  oracle_comp (singleton_spec α A ++ singleton_spec β B) (A × B) :=
do {
  x ← oc_ret ca, y ← oc_ret cb,
  x' ← oc_query (sum.inl ()) x,
  y' ← oc_query (sum.inr ()) y,
  return (x', y')
}

/-- Specifies a method for simulating an oracle for the given `oracle_comp_spec`,
  Where `S` is the type of the oracle's internal state and `o` simulates the oracle given a current state,
  eventually returning a query result and an updated state value. -/
structure simulation_oracle (spec : oracle_comp_spec) :=
(S : Type)
(o : Π (i : spec.ι), S → spec.domain i → prob_comp (spec.range i × S))
(oracle_well_formed (i : spec.ι) (s : S) (x : spec.domain i) : (o i s x).alg.well_formed)

-- instance simulation_oracle.is_well_formed {spec : oracle_comp_spec}
--   (so : simulation_oracle spec) (i : spec.ι) (s : so.S) (x : spec.domain i) :
--   (so.o i s x).well_formed :=
-- so.oracle_well_formed i s x

/-- Evaluation distribution of an `oracle_comp A B C` as a `comp A`.
`S` is the type of the internal state of the `A` to `B` oracle, and `s` is the initial state.
`o` takes the current oracle state and an `A` value, and computes a `B` value and new oracle state. -/
def simulate {spec : oracle_comp_spec} (so : simulation_oracle spec) : 
  Π {C : Type} (oc : oracle_comp spec C) (s : so.S), prob_comp (C × so.S)
| C (oc_ret c) s := do {x ← c, return (x, s)}
| C (oc_bind oc od) s := do {⟨c, s'⟩ ← simulate oc s, simulate (od c) s'}
| C (oc_query i a) s := so.o i s a

section append

/-- Combine simultation oracles two get a simulation oracle on the appended `spec`,
  using a product type to track internal states of both oracles -/
def simulation_oracle.append {spec spec' : oracle_comp_spec}
  (so : simulation_oracle spec) (so' : simulation_oracle spec') :
  simulation_oracle (spec ++ spec') :=
{ S := so.S × so'.S,
  o := λ i ⟨s, s'⟩, match i with
    | (sum.inl i) := λ x, functor.map (prod.map id (λ new_s, (new_s, s'))) (so.o i s x)
    | (sum.inr i) := λ x, functor.map (prod.map id (λ new_s', (s, new_s'))) (so'.o i s' x)
  end,
  oracle_well_formed := λ i ⟨s, s'⟩, match i with
    | (sum.inl i) := λ x, by simp [simulation_oracle.append._match_1,
        simulation_oracle.append._match_2]; sorry
    | (sum.inr i) := λ x, by simp [simulation_oracle.append._match_1,
        simulation_oracle.append._match_2]; sorry
  end }

end append

section random_oracle

/-- Return random values for any new query, returning the same value for repeated queries -/
noncomputable def random_oracle (T U : Type) 
  [decidable_eq T] [fintype U] [nonempty U] :
  simulation_oracle (singleton_spec T U) :=
{ S := list (T × U),
  o := λ _ log t, match (log.find (λ tu, prod.fst tu = t)) with
    | none := prob_comp.uniform (⊤ : finset U) (finset.univ_nonempty) >>= (λ u, return ⟨u, ⟨t, u⟩ :: log⟩)
    | (some ⟨t, u⟩) := return ⟨u, log⟩
  end,
  oracle_well_formed := λ _ log t, match (log.find (λ tu, prod.fst tu = t)) with
    | none := by simpa [random_oracle._match_1] using finset.univ_nonempty
    | (some ⟨t, u⟩) := prob_alg.return_well_formed _
  end }

end random_oracle

end oracle_comp
