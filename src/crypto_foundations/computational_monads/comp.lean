import data.bitvec.basic
import to_mathlib

/-!
# Model of Nondeterministic Computation

This file defines related notions of `comp A` and `oracle_comp B C A`,
which represent nondeterministic computations of elements of type `A`.

The support of a computation is further defined to be the possible outputs of the computation.
For the actual probability distributions of the computation, see `eval_distribution` in `dist_sem.lean`.
Well formed computations are defined so that they will have a nonempty support (making the distribution a `pmf`)
-/

/-- computational monad to extend the base language of Lean for cryptography purposes.
  `rnd n` represents a computation of purely random bits, 
  and `repeat` can repeat a random computation until some predicate holds.
  Note that because Lean doesn't have an impredicative set type, this raises universe levels -/
inductive comp : Π (A : Type), Type 1
| ret {A : Type} (a : A) : comp A
| bind {A B : Type} : Π (cb : comp B) (ca : B → comp A), comp A
| rnd (A : Type) [fA : fintype A] [iA : inhabited A] : comp A
| repeat {A : Type} : Π (p : A → Prop) [hp : decidable_pred p] (ca : comp A), comp A

@[simps]
instance comp.monad : monad comp :=
{ pure := λ A a, comp.ret a,
  bind := λ A B ca cb, comp.bind ca cb }

@[simp]
lemma comp.return_eq {A : Type} (a : A) :
  (return a : comp A) = comp.ret a :=
rfl

@[simp]
lemma comp.and_then_eq {A B : Type} (ca : comp A) (cb : comp B) :
  (ca >> cb) = ca.bind (λ _, cb) :=
rfl

namespace comp

/-- Every computation gives rise to at least one element of the return type, 
  in particular this is the result if all `rnd A` calls return `(inhabited A).default`,
  and all `repeat` calls don't check the predicate `p` at all. -/
def comp_base_exists {A : Type} (ca : comp A) : A :=
@comp.rec_on (λ A _, A) A ca
  (λ A a, a) (λ A B cb ca b fa, fa b)
  (λ A fA iA, iA.default) (λ A p hp ca a, a)

variables {A B C : Type}

section support

/-- The support of `comp A` is the elements of `A` with non-zero probability of being computed -/
def support : Π {A : Type} (ca : comp A), set A
| A (ret a) := {a}
| A (bind cb ca) := cb.support >>= (λ b, (ca b).support)
| A (@rnd _ fA iA) := ⊤
| A (@repeat _ p hp ca) := {a ∈ ca.support | p a}

@[simp]
theorem support_finite : ∀ {A : Type} (ca : comp A), ca.support.finite
| A (ret a) := set.finite_singleton a
| A (@bind _ B cb ca) := set.finite.bUnion (support_finite cb) (λ b hb, support_finite (ca b))
| A (@rnd _ fA iA) := set.univ_finite_iff_nonempty_fintype.mpr (nonempty.intro fA)
| A (@repeat _ p hp ca) := (support_finite ca).subset (λ x hx, hx.1)

@[simp] 
lemma support_ret (a : A) : 
  (ret a).support = {a} := 
rfl

@[simp]
lemma mem_support_ret (a : A) : 
  a ∈ (ret a).support :=
set.mem_singleton a

@[simp]
lemma support_bind (cb : comp B) (ca : B → comp A) :
  (cb.bind ca).support = cb.support >>= (λ b, (ca b).support) :=
rfl

@[simp]
lemma mem_support_bind_iff (cb : comp B) (ca : B → comp A) (a : A) :
  a ∈ (cb.bind ca).support ↔ ∃ b ∈ cb.support, a ∈ (ca b).support :=
by simp

lemma mem_support_bind {cb : comp B} {ca : B → comp A} (a : A)
  (b : B) (hb : b ∈ cb.support) (ha : a ∈ (ca b).support) :
  a ∈ (cb.bind ca).support :=
(mem_support_bind_iff cb ca a).2 ⟨b, hb, ha⟩

@[simp] 
lemma support_rnd [fintype A]  [inhabited A] : 
  (rnd A).support = ⊤ := 
rfl

@[simp]
lemma mem_support_rnd [fintype A] [inhabited A] (a : A) :
  a ∈ (rnd A).support :=
trivial

@[simp] 
lemma support_repeat (ca : comp A) (p : A → Prop) [decidable_pred p] :
  (repeat p ca).support = { a ∈ ca.support | p a }:= 
rfl

@[simp]
lemma mem_support_repeat_iff (ca : comp A) (p : A → Prop) [decidable_pred p] (a : A) :
  a ∈ (repeat p ca).support ↔ a ∈ ca.support ∧ p a :=
by simp

end support

section is_well_formed 

/-- A computation is well formed if both of the following conditions hold:
  1 - All sub-computations are well-formed (Trivial for `ret` and `rnd`)
  2 - The computation has non-empty support (Trivial for all but `repeat`)
  Such a computation is gaurunteed to have a non-empty support -/
@[class]
def is_well_formed : Π {A : Type}, comp A → Prop
| A (@ret _ a) := true
| A (@bind _ B cb ca) := (is_well_formed cb) ∧ (∀ b ∈ cb.support, is_well_formed (ca b))
| A (@rnd _ _ _) := true
| A (@repeat _ p hp ca) := (is_well_formed ca) ∧ (@repeat _ p hp ca).support.nonempty

@[simp]
lemma ret_is_well_formed (a : A) : 
  (ret a).is_well_formed :=
true.intro

@[simp]
lemma bind_is_well_formed_iff (cb : comp B) (ca : B → comp A) :
  (cb.bind ca).is_well_formed ↔ 
    cb.is_well_formed ∧ ∀ b ∈ cb.support, (ca b).is_well_formed :=
iff.rfl

@[simp]
lemma bind_is_well_formed_iff_left (cb : comp B)
  (ca : B → comp A) [hca : ∀ b, (ca b).is_well_formed] :
  (cb.bind ca).is_well_formed ↔ cb.is_well_formed :=
(bind_is_well_formed_iff cb ca).trans ⟨λ h, h.1, λ h, ⟨h, λ b _, hca b⟩⟩

@[simp]
lemma bind_is_well_formed_iff_right (cb : comp B) 
  [hcb : cb.is_well_formed] (ca : B → comp A) : 
  (cb.bind ca).is_well_formed ↔ ∀ b ∈ cb.support, (ca b).is_well_formed :=
(bind_is_well_formed_iff cb ca).trans ⟨λ h, h.2, λ h, ⟨hcb, h⟩⟩

lemma is_well_formed_of_bind_left {cb : comp B} {ca : B → comp A} : 
  (cb.bind ca).is_well_formed → cb.is_well_formed :=
λ h, h.1

lemma is_well_formed_of_bind_right {cb : comp B} {ca : B → comp A} :
  (cb.bind ca).is_well_formed → ∀ b ∈ cb.support, (ca b).is_well_formed :=
λ h, h.2

@[simp]
lemma rnd_is_well_formed (A : Type) [fintype A] [inhabited A] :
  (rnd A).is_well_formed :=
true.intro

@[simp]
lemma repeat_is_well_formed_iff (ca : comp A) (p : A → Prop) [decidable_pred p] :
  (ca.repeat p).is_well_formed ↔ 
    ca.is_well_formed ∧ (ca.repeat p).support.nonempty :=
iff.rfl

lemma repeat_is_well_formed (p : A → Prop) [decidable_pred p]
  (ca : comp A) (hca : is_well_formed ca)
  (hpca : (repeat p ca).support.nonempty) :
  (ca.repeat p).is_well_formed :=
by simp only [is_well_formed, hca, hpca, true_and]

instance ret.is_well_formed {A : Type} (a : A) :
  (ret a).is_well_formed :=
by simp [is_well_formed]

instance monad.return.is_well_formed {A : Type} (a : A) :
  (return a : comp A).is_well_formed :=
by simp

instance bind.is_well_formed {A B : Type} (cb : comp B) (ca : B → comp A)
  [hcb : cb.is_well_formed] [hca : ∀ b, (ca b).is_well_formed] :
  (cb.bind ca).is_well_formed :=
by simp [is_well_formed, hcb, hca]

instance monad.bind.is_well_formed {A B : Type} (cb : comp B) (ca : B → comp A)
  [hcb : cb.is_well_formed] [hca : ∀ b, (ca b).is_well_formed] :
  (cb >>= ca).is_well_formed :=
by simp [hca]

instance monad.and_then.is_well_formed {A B : Type} (cb : comp B) (ca : comp A)
  [hcb : cb.is_well_formed] [hca : ca.is_well_formed] :
  (cb >> ca).is_well_formed :=
by simp [is_well_formed, hcb, hca]

instance rnd.is_well_formed (A : Type) [inhabited A] [fintype A] :
  (rnd A).is_well_formed :=
by simp [is_well_formed]

theorem support_nonempty_of_well_formed : ∀ {A : Type} (ca : comp A)
  [h : ca.is_well_formed], ca.support.nonempty
| A (ret a) h := ⟨a, mem_support_ret a⟩
| A (@bind _ B cb ca) h := 
    let ⟨b, hb⟩ := @support_nonempty_of_well_formed B cb h.1 in
    let ⟨a, ha⟩ := @support_nonempty_of_well_formed A (ca b) (h.2 b hb) in
    ⟨a, mem_support_bind a b hb ha⟩
| A (@rnd _ fA hA) h := ⟨@arbitrary A hA, @mem_support_rnd A fA hA _⟩
| A (@repeat _ p hp ca) h := h.2

end is_well_formed

end comp

