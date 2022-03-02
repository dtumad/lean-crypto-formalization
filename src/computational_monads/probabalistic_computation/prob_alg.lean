import measure_theory.probability_mass_function.constructions

open vector

open_locale classical big_operators nnreal ennreal

variables {A B : Type}

/-- computational monad to extend the base language of Lean for modeling cryptographic algorithms.
  Note that because Lean doesn't have an impredicative base type, this raises universe levels.

  `pure' A a` represents returning a value `a : A`
  `bind' A B ca cb` represents running `ca : prob_comp A`,
    passing the result to `cb`, and running the result.
  `coin` represents sampling between `tt : bool` and `ff : bool` with equal probability.
  `repeat p ca` represents running `ca` until the output satisfies `p` 
  
  TODO: Can build implementation up from `random_gen` interface?
  -/
inductive prob_alg : Π (A : Type), Type 1
-- | uniform {A : Type u} (bag : finset A) : prob_alg A
| pure' (A : Type) (a : A) : prob_alg A
| bind' (A B : Type) (ca : prob_alg A) (cb : A → prob_alg B) : prob_alg B
| coin : prob_alg bool -- This could maybe use `pmf.bernoulli` to allow "unfair" coins
| repeat {A : Type} (ca : prob_alg A) (p : A → Prop) : prob_alg A

namespace prob_alg

variables (ca ca' : prob_alg A) (cb : A → prob_alg B)

section monad

/-- Create a monad structure, using uniform sampling from a singleton set as `return` -/
@[simps]
instance monad : monad prob_alg :=
{ pure := pure',
  bind := bind' }

@[simp] lemma return_eq_pure' (a : A) :
  (return a : prob_alg A) = pure' A a := rfl

end monad

example (n m : ℕ) : prob_alg ℕ := do { 
  b ← coin, b' ← coin,
  x ← if b ∧ b' then return n else return m,
  y ← return (if b ∨ b' then m * x else n * x),
  return (x + y) 
}

section support

/-- The support of `ca : prob_comp A` is the set outputs in `A` with non-zero probability -/
def support : Π {A : Type}, prob_alg A → set A
| _ (pure' A a) := {a}
| _ (bind' A B ca cb) := ⋃ a ∈ ca.support, (cb a).support
| bool coin := ⊤
| A (repeat ca p) := {a ∈ ca.support | p a}

@[simp] lemma support_pure' (a : A) :
  support (pure' A a) = {a} := rfl

@[simp] lemma mem_support_pure'_iff (a a' : A) :
  a ∈ (pure' A a').support ↔ a = a' := iff.rfl

lemma support_return (a : A) :
  support (return a) = {a} := support_pure' a

lemma mem_support_return_iff (a a' : A) :
  a ∈ support (return a') ↔ a = a':= by simp

@[simp] lemma support_bind' :
  (bind' A B ca cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

lemma mem_support_bind'_iff (b : B) : 
  b ∈ (bind' A B ca cb).support ↔ ∃ a ∈ ca.support, b ∈ (cb a).support := by simp

lemma support_bind :
  (ca >>= cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

lemma mem_support_bind_iff (b : B) :
  b ∈ (ca >>= cb).support ↔ ∃ a ∈ ca.support, b ∈ (cb a).support := by simp

@[simp] lemma support_coin : support coin = ⊤ := rfl

@[simp] lemma mem_support_coin (b : bool) : b ∈ coin.support := set.mem_univ b

@[simp] lemma support_repeat (p : A → Prop) :
  (ca.repeat p).support = {a ∈ ca.support | p a} :=  rfl

lemma mem_support_repeat_iff (a : A) (p : A → Prop) :
  a ∈ (ca.repeat p).support ↔ a ∈ ca.support ∧ p a := iff.rfl

end support

section well_formed

/-- `well_formed ca` says that `ca` has at least one possible output, needed to define evalutaion.
  In particular, for any `uniform bag` step `bag` must be nonempty,
  and for each `repeat p ca` there must be some output of `ca` satisfying `p` -/
def well_formed : Π {A : Type}, prob_alg A → Prop
| _ (pure' A a) := true
| _ (bind' A B ca cb) := ca.well_formed ∧ ∀ a ∈ ca.support, (cb a).well_formed
| _ coin := true
| A (repeat ca p) := ca.well_formed ∧ ∃ a ∈ ca.support, p a

/-- The `well_formed` predicate is equivalent to having nonempty support -/
lemma support_nonempty_of_well_formed :
  Π {A : Type} (ca : prob_alg A), ca.well_formed → ca.support.nonempty
| _ (pure' A a) uniform_wf := set.singleton_nonempty a
| _ (bind' A B ca cb) bind_wf := 
    let ⟨ca_wf, cb_wf⟩ := bind_wf in
    let ⟨a, ha⟩ := support_nonempty_of_well_formed ca ca_wf in
    let ⟨b, hb⟩ := support_nonempty_of_well_formed (cb a) (cb_wf a ha) in
    set.nonempty_Union.2 ⟨a, set.nonempty_Union.2 ⟨ha, ⟨b, hb⟩⟩⟩
| _ coin coin_wf := set.univ_nonempty
| A (repeat ca p) repeat_wf := let ⟨ca_wf, ⟨a, ha, hpa⟩⟩ := repeat_wf in ⟨a, ⟨ha, hpa⟩⟩

@[simp] lemma pure'_well_formed (a : A) :
  (pure' A a).well_formed := true.intro

@[simp] lemma return_well_formed (a : A) :
  (return a : prob_alg A).well_formed := true.intro

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

@[simp] lemma coin_well_formed : coin.well_formed := true.intro

@[simp] lemma repeat_well_formed_iff (p : A → Prop) :
  (repeat ca p).well_formed ↔ ca.well_formed ∧ ∃ a ∈ ca.support, p a := iff.rfl

lemma repeat_well_formed {ca : prob_alg A} {p : A → Prop}
  (hca : ca.well_formed) (hp : ∃ a ∈ ca.support, p a) :
  (repeat ca p).well_formed := ⟨hca, hp⟩

lemma well_formed_of_repeat_well_formed {ca : prob_alg A} {p : A → Prop} :
  (repeat ca p).well_formed → well_formed ca | h := h.1

lemma exists_mem_support_of_repeat_well_formed {ca : prob_alg A} {p : A → Prop} :
  (repeat ca p).well_formed → ∃ a ∈ ca.support, p a | h := h.2

example (z : ℕ) : well_formed 
  (do x ← return (z + 3),
      y ← return (x * z), 
      b ← coin,
      return (if b then 0 else x + y + z)) := by simp

end well_formed

end prob_alg