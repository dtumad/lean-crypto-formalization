import measure_theory.probability_mass_function.constructions

open_locale classical big_operators nnreal ennreal

variables {A B : Type}

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

section monad

/-- Create a monad structure, using uniform sampling from a singleton set as `return` -/
@[simps]
instance monad : monad prob_alg :=
{ pure := λ A a, uniform {a},
  bind := bind' }

@[simp] lemma return_eq_uniform_singleton (a : A) :
  (return a : prob_alg A) = uniform {a} :=
rfl

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

@[simp] lemma support_uniform (bag : finset A) :
  (uniform bag).support = ↑bag :=
rfl

lemma mem_support_uniform_iff (a : A) (bag : finset A) :
  a ∈ (uniform bag).support ↔ a ∈ bag :=
iff.rfl

lemma support_return (a : A) :
  support (return a) = ({a} : finset A) :=
support_uniform {a}

lemma mem_support_return_iff (a a' : A) :
  a ∈ support (return a') ↔ a = a':=
by simp

@[simp] lemma support_bind' :
  (bind' A B ca cb).support = ⋃ a ∈ ca.support, (cb a).support :=
rfl

lemma mem_support_bind'_iff (b : B) : 
  b ∈ (bind' A B ca cb).support ↔ ∃ a ∈ ca.support, b ∈ (cb a).support :=
by simp

lemma support_bind :
  (ca >>= cb).support = ⋃ a ∈ ca.support, (cb a).support :=
rfl

lemma mem_support_bind_iff (b : B) :
  b ∈ (ca >>= cb).support ↔ ∃ a ∈ ca.support, b ∈ (cb a).support :=
by simp

@[simp] lemma support_repeat (p : A → Prop) :
  (ca.repeat p).support = {a ∈ ca.support | p a} := 
rfl

lemma mem_support_repeat_iff (a : A) (p : A → Prop) :
  a ∈ (ca.repeat p).support ↔ a ∈ ca.support ∧ p a := 
iff.rfl

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

@[simp] lemma uniform_well_formed_iff (bag : finset A) :
  (uniform bag).well_formed ↔ bag.nonempty := 
iff.rfl

lemma uniform_well_formed {bag : finset A} (hbag : bag.nonempty) :
  (uniform bag).well_formed :=
hbag

lemma uniform_singleton_well_formed (a : A) :
  (uniform ({a} : finset A)).well_formed :=
uniform_well_formed (finset.singleton_nonempty a)

lemma uniform_insert_well_formed [decidable_eq A] (a : A) (bag : finset A) :
  (uniform (insert a bag)).well_formed := 
uniform_well_formed (finset.insert_nonempty a bag)

lemma nonempty_of_uniform_well_formed (bag : finset A) :
  (uniform bag).well_formed → bag.nonempty
| h := h

@[simp] lemma return_well_formed (a : A) :
  (return a : prob_alg A).well_formed :=
⟨a, finset.mem_singleton_self a⟩

@[simp] lemma bind'_well_formed_iff :
  (bind' A B ca cb).well_formed ↔ ca.well_formed ∧ ∀ a ∈ ca.support, (cb a).well_formed :=
iff.rfl

lemma bind'_well_formed {ca : prob_alg A} {cb : A → prob_alg B}
  (hca : ca.well_formed) (hcb : ∀ a ∈ ca.support, (cb a).well_formed) :
  (bind' A B ca cb).well_formed :=
⟨hca, hcb⟩

@[simp] lemma bind_well_formed_iff :
  (ca >>= cb).well_formed ↔ ca.well_formed ∧ ∀ a ∈ ca.support, (cb a).well_formed :=
iff.rfl

lemma bind_well_formed {ca : prob_alg A} {cb : A → prob_alg B}
  (hca : ca.well_formed) (hcb : ∀ a ∈ ca.support, (cb a).well_formed) :
  (ca >>= cb).well_formed :=
⟨hca, hcb⟩

@[simp] lemma repeat_well_formed_iff (p : A → Prop) :
  (repeat ca p).well_formed ↔ ca.well_formed ∧ ∃ a ∈ ca.support, p a :=
iff.rfl

lemma repeat_well_formed {ca : prob_alg A} {p : A → Prop}
  (hca : ca.well_formed) (hp : ∃ a ∈ ca.support, p a) :
  (repeat ca p).well_formed := 
⟨hca, hp⟩

lemma well_formed_of_repeat_well_formed {ca : prob_alg A} {p : A → Prop} :
  (repeat ca p).well_formed → well_formed ca
| h := h.1

lemma exists_mem_support_of_repeat_well_formed {ca : prob_alg A} {p : A → Prop} :
  (repeat ca p).well_formed → ∃ a ∈ ca.support, p a
| h := h.2

example (z : ℕ) : well_formed 
  (do x ← return (z + 3),
      y ← return (x * z), 
      return (x + y + z)) := by simp

end well_formed

end prob_alg