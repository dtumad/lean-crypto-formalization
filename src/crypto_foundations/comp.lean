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
| ret {A : Type} [hA : decidable_eq A] (a : A) : comp A
| bind {A B : Type} : Π (cb : comp B) (ca : B → comp A), comp A
| rnd (A : Type) [hA : decidable_eq A] [fA : fintype A] [iA : inhabited A] : comp A
| repeat {A : Type} : Π (p : A → Prop) [hp : decidable_pred p] (ca : comp A) , comp A

namespace comp

variables {A B C : Type}

/-- Every computation gives rise to at least one element of the return type, 
  in particular this is the result if all `rnd` calls return strings of `1` bits. -/
def comp_base_exists (ca : comp A) : A :=
@comp.rec_on (λ A _, A) A ca
  (λ A hA a, a) (λ A B cb ca b fa, fa b)
  (λ A hA fA iA, iA.default) (λ A p hp ca a, a)

/-- Because only `ret` and `rnd` terminate computation, and `ret` requires `decidable_eq A`,
  every computation must return a type with decidable equality.
  This needs to be definitional to make `support` fully computable -/
def decidable_eq_of_comp (ca : comp A) : decidable_eq A :=
@comp.rec_on (λ A _, decidable_eq A) A ca
  (λ A hA a, hA) (λ A B cb ca hcb hca, hca cb.comp_base_exists)
  (λ A hA fA iA, hA) (λ A p hp ca h, h)

/-- alias because this situation is very common due to use of `bUnion` in support -/
def decidable_eq_of_comp' (cb : comp B) (ca : B → comp A) : decidable_eq A :=
comp.decidable_eq_of_comp $ bind cb ca

section support

/-- The support of `comp A` is the elements of `A` with non-zero probability of being computed -/
def support : Π {A : Type}, comp A → finset A
| A (@ret A' hA' a) := {a}
| A (@bind A' B cb ca) := @finset.bUnion B A (decidable_eq_of_comp' cb ca) 
    (support cb) (λ b, support $ ca b)
| A (@rnd A' hA fA iA) := @finset.univ A fA
| A (@repeat A' p hp ca) := @finset.filter _ p hp (support ca)

@[simp] lemma support_ret [decidable_eq A] (a : A) :
  (ret a).support = {a} := rfl

@[simp] lemma mem_support_ret_iff [decidable_eq A] (a a' : A) : 
  a ∈ (ret a').support ↔ a = a' := by simp

@[simp] lemma support_bind (cb : comp B) (ca : B → comp A) :
  (bind cb ca).support = @finset.bUnion B A (decidable_eq_of_comp' cb ca) 
    cb.support (λ b, (ca b).support) := rfl

@[simp] lemma mem_support_bind_iff (cb : comp B) (ca : B → comp A) (a : A) :
  a ∈ (comp.bind cb ca).support ↔ ∃ (b : B), b ∈ cb.support ∧ a ∈ (ca b).support := by simp

@[simp] lemma support_rnd [inhabited A] [fintype A] [decidable_eq A] : 
  (rnd A).support = finset.univ := rfl

@[simp] lemma mem_support_rnd [inhabited A] [fintype A] [decidable_eq A] (a : A) : 
  a ∈ (rnd A).support := by simp

@[simp] lemma support_repeat (ca : comp A) (p : A → Prop) [decidable_pred p] :
  (repeat p ca).support = ca.support.filter p := rfl

@[simp] lemma mem_support_repeat (ca : comp A) (p : A → Prop) [decidable_pred p] (a : A) :
  a ∈ (repeat p ca).support ↔ a ∈ ca.support ∧ p a := by simp

@[simp] lemma support_bind_ret [decidable_eq A] (a : A) (cb : A → comp B) :
  ((ret a).bind cb).support = (cb a).support :=
by rw [support_bind, support_ret, finset.singleton_bUnion]

@[simp] lemma mem_support_bind_ret [decidable_eq A] (a : A) (cb : A → comp B) (b : B) :
  b ∈ ((ret a).bind cb).support ↔ b ∈ (cb a).support :=
by simp

@[simp] lemma support_bind_rnd [inhabited A] [fintype A] [decidable_eq A] [decidable_eq B]
  (cb : A → comp B) : ((rnd A).bind cb).support = finset.bUnion finset.univ (λ a, (cb a).support) :=
begin
  simp [support_rnd, support_bind],
  congr,
end

@[simp] lemma mem_support_bind_rnd [inhabited A] [fintype A] [decidable_eq A] [decidable_eq B]
  (cb : A → comp B) (b : B) : b ∈ ((rnd A).bind cb).support ↔ ∃ a, b ∈ (cb a).support :=
by simp

end support

section is_well_formed 

/-- A computation is well formed if both of the following conditions hold:
  1 - All sub-computations are well-formed (Trivial for `ret` and `rnd`)
  2 - The computation has non-empty support (Trivial for all but `repeat`)
  Such a computation is gaurunteed to have a non-empty support 
  TODO: Try and make this instance based wherever possible -/
@[class]
inductive is_well_formed : ∀ {A : Type}, comp A → Prop
| well_formed_ret {A : Type} [hA : decidable_eq A] (a : A) :
    is_well_formed (@ret A hA a)
| well_formed_bind {A B : Type} (cb : comp B) (ca : B → comp A) 
    (hcb : is_well_formed cb) (hca : ∀ b ∈ cb.support, is_well_formed (ca b)) :
    is_well_formed (bind cb ca)
| well_formed_rnd {A : Type} [inhabited A] [fintype A] [decidable_eq A] :
    is_well_formed (rnd A)
| well_formed_repeat {A : Type} (p : A → Prop) [decidable_pred p] (ca : comp A)
    (hca : is_well_formed ca) (hpca : (repeat p ca).support.nonempty) :
    is_well_formed (repeat p ca)

open is_well_formed

@[simp] lemma is_well_formed_ret [decidable_eq A] (a : A) : 
  is_well_formed (ret a) :=
well_formed_ret a

instance ret.is_well_formed {A : Type} [decidable_eq A] (a : A) :
  (ret a).is_well_formed :=
by simp

instance bind.is_well_formed_of_all_well_formed {A B : Type} (cb : comp B) [hcb : cb.is_well_formed] 
  (ca : B → comp A) [hca : ∀ b, (ca b).is_well_formed] :
  (cb.bind ca).is_well_formed :=
well_formed_bind cb ca hcb (by apply_instance)

@[simp] lemma is_well_formed_bind_iff (cb : comp B) (ca : B → comp A) :
  is_well_formed (cb.bind ca) ↔ 
    is_well_formed cb ∧ ∀ b ∈ cb.support, is_well_formed (ca b) :=
begin
  refine ⟨λ w, _, λ h, well_formed_bind cb ca h.1 h.2⟩,
  cases w,
  split; assumption,
end

@[simp] lemma is_well_formed_bind_iff' (cb : comp B) [h : cb.is_well_formed] (ca : B → comp A) :
  is_well_formed (cb.bind ca) ↔ ∀ b ∈ cb.support, is_well_formed (ca b) :=
by simp [h]

@[simp] lemma is_well_formed_rnd [inhabited A] [fintype A] [decidable_eq A] : 
  is_well_formed (rnd A) :=
well_formed_rnd

instance rnd.is_well_formed {A : Type} [inhabited A] [fintype A] [decidable_eq A] :
  (rnd A).is_well_formed :=
by simp

@[simp] lemma is_well_formed_repeat_iff (p : A → Prop) [hp : decidable_pred p] (ca : comp A) :
  is_well_formed (@repeat A p hp ca) ↔ is_well_formed ca ∧ (repeat p ca).support.nonempty :=
begin
  refine ⟨λ w, _, λ h, well_formed_repeat p ca h.1 h.2⟩,
  tactic.unfreeze_local_instances,
  cases w,
  split; assumption,
end

theorem support_nonempty_of_well_formed (ca : comp A)
  [hca : ca.is_well_formed] : ca.support.nonempty :=
begin
  tactic.unfreeze_local_instances,
  induction hca with _ _ _ _ _ cb ca _ _ hcb_ih hca_ih A hA fA dA _ _ _ _ _ ha _,
  { simp },
  { obtain ⟨b, hb⟩ := hcb_ih,
    obtain ⟨a, ha⟩ := hca_ih b hb,
    exact ⟨a, (mem_support_bind_iff cb ca a).2 ⟨b, hb, ha⟩⟩ },
  { exact ⟨@arbitrary A hA, @mem_support_rnd A hA fA dA _⟩ },
  { exact ha },
end

end is_well_formed

end comp

