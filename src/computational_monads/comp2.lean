import to_mathlib
import measure_theory.probability_mass_function.constructions

/-- computational monad to extend the base language of Lean for modeling cryptographic algorithms.
  Note that because Lean doesn't have an impredicative base type, this raises universe levels.
  `uniform bag` represents uniformly randomly sampling an element of the finite set `bag`.
  `bind ca cb` represents running `ca`, passing the result to `cb`, and running the result.
  `repeat p ca` represents running `ca` until the output satisfies `p` -/
inductive prob_comp : Π (A : Type), Type 1
| uniform {A : Type} (bag : finset A) : prob_comp A
| bind {A B : Type} (ca : prob_comp A) (cb : A → prob_comp B) : prob_comp B
| repeat {A : Type} (p : A → Prop) (ca : prob_comp A) : prob_comp A

/-- Create a monad structure, using uniform sampling from a singleton set as `return` -/
@[simps]
instance prob_comp.monad : monad prob_comp :=
{ pure := λ A a, prob_comp.uniform {a},
  bind := λ A B, prob_comp.bind }

/-- Example of a computation computing the sum of a random odd element and random even element -/
example : prob_comp ℕ :=
let nums : finset ℕ := {1, 2, 3, 4, 5} in
do x ← prob_comp.repeat odd (prob_comp.uniform nums),
  y ← prob_comp.repeat even (prob_comp.uniform nums),
  return (x + y)

namespace prob_comp

variables {A B C : Type}

section support

/-- The support of `ca : prob_comp A` is the set outputs in `A` with non-zero probability -/
def support : Π {A : Type}, prob_comp A → set A
| _ (uniform bag) := ↑bag
| _ (bind ca cb) := ⋃ a ∈ ca.support, (cb a).support
| _ (repeat p ca) := {a ∈ ca.support | p a}

@[simp] lemma support_uniform (bag : finset A) :
  (uniform bag).support = ↑bag := rfl

lemma mem_support_uniform_iff (bag : finset A)
  (a : A) : a ∈ (uniform bag).support ↔ a ∈ bag := iff.rfl

@[simp] lemma support_bind (ca : prob_comp A) (cb : A → prob_comp B) :
  (ca.bind cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

lemma mem_support_bind_iff (ca : prob_comp A) (cb : A → prob_comp B)
  (b : B) : b ∈ (ca.bind cb).support ↔ ∃ a ∈ ca.support, b ∈ (cb a).support := by simp

@[simp] lemma support_repeat (p : A → Prop) (ca : prob_comp A) :
  (repeat p ca).support = {a ∈ ca.support | p a} := rfl

lemma mem_support_repeat_iff (p : A → Prop) (ca : prob_comp A)
  (a : A) : a ∈ (repeat p ca).support ↔ a ∈ ca.support ∧ p a := by simp

end support

section well_formed

/-- `well_formed ca` says that `ca` has at least one possible output, needed to define evalutaion.
  In particular, for any `uniform bag` step `bag` must be nonempty,
  and for each `repeat p ca` there must be some output of `ca` satisfying `p` -/
@[class]
def well_formed : Π {A : Type}, prob_comp A → Prop
| A (uniform bag) := bag.nonempty
| A (bind ca cb) := ca.well_formed ∧ ∀ a ∈ ca.support, (cb a).well_formed
| A (repeat p ca) := ca.well_formed ∧ ∃ a ∈ ca.support, p a

/-- The `well_formed` predicate is equivalent to having nonempty support -/
lemma support_nonempty_of_well_formed :
  Π {A : Type} (ca : prob_comp A), ca.well_formed → ca.support.nonempty
| A (uniform bag) uniform_wf := uniform_wf
| B (@bind A _ ca cb) bind_wf := 
    let ⟨ca_wf, cb_wf⟩ := bind_wf in
    let ⟨a, ha⟩ := support_nonempty_of_well_formed ca ca_wf in
    let ⟨b, hb⟩ := support_nonempty_of_well_formed (cb a) (cb_wf a ha) in
    set.nonempty_Union.2 ⟨a, set.nonempty_Union.2 ⟨ha, ⟨b, hb⟩⟩⟩
| A (repeat p ca) repeat_wf := let ⟨ca_wf, ⟨a, ha, hpa⟩⟩ := repeat_wf in ⟨a, ⟨ha, hpa⟩⟩

end well_formed

section eval_distribution

/-- Private definition used to bootstrap the actual evalution function.
  The reason this is to equate the `pmf` supports with the `prob_comp` supports -/
private noncomputable def eval_distribution' :
  Π {A : Type} (ca : prob_comp A) (ca_wf : ca.well_formed), 
    Σ (pa : pmf A), plift (∀ (a : A), (a ∈ pa.support ↔ a ∈ ca.support))
| A (uniform bag) uniform_wf :=
  ⟨pmf.uniform_of_finset bag uniform_wf,
    plift.up $ pmf.mem_support_uniform_of_finset_iff uniform_wf⟩
| B (@bind A _ ca cb) bind_wf :=
  let pa := eval_distribution' ca bind_wf.1 in
  let pb := λ a ha, eval_distribution' (cb a) (bind_wf.2 a ha) in
  ⟨pa.1.bind_on_support $ λ a ha, (pb a $ ((plift.down pa.2) a).1 ha).1,
    plift.up $ λ b, begin
      simp only [pmf.mem_support_bind_on_support_iff, mem_support_bind_iff, plift.down pa.2],
      split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩; simpa [(plift.down (pb a ha).2) b] using ha'
    end⟩
| A (repeat p ca) repeat_wf :=
  let ⟨ca_wf, hp⟩ := repeat_wf in
  let ⟨pa, hpa⟩ := eval_distribution' ca ca_wf in
  ⟨pa.filter p (let ⟨a, ha, hap⟩ := hp in ⟨a, hap, (plift.down hpa a).2 ha⟩),
    plift.up $ λ a, (pmf.mem_support_filter_iff _ a).trans
      (by rw [plift.down hpa a]; exact and_comm (p a) (a ∈ ca.support))⟩

/-- Denotational semantics for evaluation of a `prob_comp A`, as a probability distribution.
  The distribution is given by a probability mass function `pmf A` on the underlying type.
  This requires providing a proof of well formedness to ensure the distribution sums to `1`.-/
noncomputable def eval_distribution (ca : prob_comp A) [ca.well_formed] :
  pmf A := (eval_distribution' ca $ by apply_instance).1

@[simp]
theorem support_eval_distribution_eq_support (ca : prob_comp A) [ca.well_formed] :
  ca.eval_distribution.support = ca.support :=
set.ext (plift.down (eval_distribution' ca $ by apply_instance).snd)

section prob_event

/-- The probability of an event holding on the result of a probablistic computation.
  The definition is in terms of the `outer_measure` structure induced by the `eval_distribution`.
  This is equivalent to the sum of the probabilities of each element of the set. -/
noncomputable def prob_event (ca : prob_comp A) [ca.well_formed]
  (event : set A) : ennreal :=
ca.eval_distribution.to_outer_measure event

end prob_event

end eval_distribution





-- TODO: This works, but it gets kind of messy. Might not be worth computability
-- section decidable

-- @[class]
-- inductive decidable : Π {A : Type}, prob_comp A → Type 1
-- | decidable_uniform {A : Type} (bag : finset A)
--     (hA : decidable_eq A) : decidable (uniform bag)
-- | decidable_bind {A B : Type} (ca : prob_comp A) (cb : A → prob_comp B)
--     (hca : decidable ca) (hcb : ∀ a ∈ ca.support, decidable (cb a)) : decidable (bind ca cb)
-- | decidable_repeat {A : Type} (hA : decidable_eq A) (p : A → Prop) (ca : prob_comp A)
--     (hp : decidable_pred p) (hca : decidable ca) : decidable (repeat p ca)

-- open decidable

-- def decidable_equality_of_prob_comp (ca : prob_comp A)
--   [ca.well_formed] (dec_ca : decidable ca) : A

-- /-- Computable version of `prob_comp.support`, returning a `finset` insead of a finite `set`.
--   This requires decidable instances on binding types and decidability of loop predicates. -/
-- def finsupport : Π {A : Type} (ca : prob_comp A) [decidable ca], finset A
-- | A (uniform bag) (decidable_uniform _ hA):= bag
-- | B (@bind A _ ca cb) (decidable_bind _ _ hca hcb) :=
--     by have h : decidable_eq B := sorry;
--     exactI ca.finsupport.bUnion (λ a, (cb a).finsupport)
-- | A (repeat p ca) _ := ca.finsupport.

-- end decidable

end prob_comp
