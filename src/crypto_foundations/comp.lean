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
| repeat {A : Type} : Π (p : A → Prop) [hp : decidable_pred p] (ca : comp A) , comp A

@[simps]
instance comp.monad : monad comp :=
{ pure := λ A a, comp.ret a,
  bind := λ A B ca cb, comp.bind ca cb }

@[simp]
lemma comp.return_eq {A : Type} (a : A) :
  (return a : comp A) = comp.ret a :=
rfl

namespace comp

/-- Every computation gives rise to at least one element of the return type, 
  in particular this is the result if all `rnd` calls return strings of `1` bits. -/
def comp_base_exists {A : Type} (ca : comp A) : A :=
@comp.rec_on (λ A _, A) A ca
  (λ A a, a) (λ A B cb ca b fa, fa b)
  (λ A fA iA, iA.default) (λ A p hp ca a, a)

-- class inductive decidable_comp : Π {A : Type}, comp A → Type 1
-- | dc_ret {A : Type} (a : A) (hA : decidable_eq A) : 
--     decidable_comp (ret a)
-- | dc_bind {A B : Type} {cb : comp B} {ca : B → comp A}
--       (hcb : decidable_comp cb) (hca : Π b, decidable_comp $ ca b) : 
--     decidable_comp (cb.bind ca)
-- | dc_rnd (A : Type) [fA : fintype A] [iA : inhabited A] (hA : decidable_eq A) :
--     decidable_comp (rnd A)
-- | dc_repeat {A : Type} (p : A → Prop) [hp : decidable_pred p] 
--       (ca : comp A) (hca : decidable_comp ca) :
--     decidable_comp (repeat p ca)

-- namespace decidable_comp

-- def decidable_comp_of_bind_left {A B : Type} {cb : comp B} {ca : B → comp A} : 
--   Π (h : (cb.bind ca).decidable_comp), cb.decidable_comp
-- | (dc_bind hcb hca) := hcb

-- @[simp]
-- lemma decidable_comp_of_bind_left_apply {A B : Type} {cb : comp B} {ca : B → comp A}
--   (hcb : decidable_comp cb) (hca : Π b, decidable_comp $ ca b) :
--   @decidable_comp_of_bind_left A B cb ca (dc_bind hcb hca) = hcb :=
-- rfl

-- def decidable_comp_of_bind_right {A B : Type} {cb : comp B} {ca : B → comp A} : 
--   Π (h : (cb.bind ca).decidable_comp) (b : B), (ca b).decidable_comp
-- | (dc_bind hcb hca) := hca

-- @[simp]
-- lemma decidable_comp_of_bind_right_apply {A B : Type} {cb : comp B} {ca : B → comp A}
--   (hcb : decidable_comp cb) (hca : Π b, decidable_comp $ ca b) (b : B) :
--   @decidable_comp_of_bind_right A B cb ca (dc_bind hcb hca) = hca :=
-- rfl

-- def decidable_comp_of_repeat {A : Type} {p : A → Prop} : Π [hp : decidable_pred p] {ca : comp A}
--   (hca : (@repeat A p hp ca).decidable_comp), ca.decidable_comp
-- | hp ca (@dc_repeat A p _ _ h) := h

-- instance decidable_comp_ret {A : Type} (a : A) [hA : decidable_eq A] :
--   decidable_comp (ret a) :=
-- dc_ret a hA

-- instance decidable_comp_bind {A B : Type} (cb : comp B) (ca : B → comp A)
--   [hcb : decidable_comp cb] [hca : ∀ b, decidable_comp (ca b)] :
--   decidable_comp (bind cb ca) :=
-- dc_bind hcb hca

-- instance decidable_comp_rnd {A : Type} [fintype A] [inhabited A]
--   [hA : decidable_eq A] : decidable_comp (rnd A) :=
-- dc_rnd A hA

-- instance decidable_comp_repeat {A : Type} (p : A → Prop) [decidable_pred p]
--   (ca : comp A) [hca : decidable_comp ca] : decidable_comp (repeat p ca) :=
-- dc_repeat p ca hca

-- def decidable_eq_of_decidable_comp :
--   Π {A : Type} (ca : comp A) (hca : decidable_comp ca), decidable_eq A
-- | A (ret a) (dc_ret _ h) := h
-- | A (bind cb ca) (dc_bind hcb hca) :=
--     @decidable_eq_of_decidable_comp A (ca (comp_base_exists cb)) (hca _)
-- | A (@rnd _ fA iA) (@dc_rnd _ _ _ h) := h
-- | A (@repeat _ p hp ca) (@dc_repeat _ _ _ _ h) := @decidable_eq_of_decidable_comp A ca h

-- def decidable_eq_of_bind {A B : Type} (cb : comp B) [hcb : decidable_comp cb] 
--   (ca : B → comp A) [hca : ∀ b, decidable_comp $ ca b] : decidable_eq A := 
-- @decidable_eq_of_decidable_comp A (ca $ comp_base_exists cb) (hca _)

-- end decidable_comp

variables {A B C : Type}

-- /-- Because only `ret` and `rnd` terminate computation, and `ret` requires `decidable_eq A`,
--   every computation must return a type with decidable equality.
--   This needs to be definitional to make `support` fully computable -/
-- def decidable_eq_of_comp (ca : comp A) : decidable_eq A :=
-- @comp.rec_on (λ A _, decidable_eq A) A ca
--   (λ A hA a, hA) (λ A B cb ca hcb hca, hca cb.comp_base_exists)
--   (λ A hA fA iA, hA) (λ A p hp ca h, h)

-- /-- alias because this situation is very common due to use of `bUnion` in support -/
-- def decidable_eq_of_comp' (cb : comp B) (ca : B → comp A) : decidable_eq A :=
-- comp.decidable_eq_of_comp $ bind cb ca

section support

-- /-- The support of `comp A` is the elements of `A` with non-zero probability of being computed -/
-- def support : Π {A : Type} (ca : comp A), set A
-- | A (ret a) := {a}
-- | A (bind cb ca) := (support cb) >>= (λ b, support $ ca b)
--   -- @finset.bUnion B A (@decidable_comp.decidable_eq_of_bind A B cb h.decidable_comp_of_bind_left ca h.decidable_comp_of_bind_right) 
--   --   (@support B cb h.decidable_comp_of_bind_left) (λ b, @support A (ca b) (h.decidable_comp_of_bind_right b))
-- | A (@rnd _ fA iA) _ := @finset.univ A fA
-- | A (@repeat _ p hp ca) (@decidable_comp.dc_repeat _ _ _ _ h) := 
--   @finset.filter _ p hp (@support A ca h)

/-- The support of `comp A` is the elements of `A` with non-zero probability of being computed -/
def support : Π {A : Type} (ca : comp A), set A
| A (ret a) := {a}
| A (bind cb ca) := cb.support >>= (λ b, (ca b).support)
| A (@rnd _ fA iA) := ⊤
| A (@repeat _ p hp ca) := {a ∈ ca.support | p a}

@[simp] 
lemma support_ret (a : A) :
  (ret a).support = {a} := 
rfl

@[simp]
lemma support_bind (cb : comp B) (ca : B → comp A) :
  (cb.bind ca).support = cb.support >>= (λ b, (ca b).support) :=
rfl

@[simp]
lemma mem_support_bind_iff (cb : comp B) (ca : B → comp A) (a : A) :
  a ∈ (cb.bind ca).support ↔ ∃ b ∈ cb.support, a ∈ (ca b).support :=
by simp

@[simp] 
lemma support_rnd [inhabited A] [fintype A] : 
  (rnd A).support = ⊤ := 
rfl

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
class inductive is_well_formed : 
  ∀ {A : Type} (ca : comp A), Prop
| well_formed_ret {A : Type} (a : A) :
    is_well_formed (@ret A a)
| well_formed_bind {A B : Type} (cb : comp B) (ca : B → comp A) 
      (hcb : is_well_formed cb) (hca : ∀ b ∈ cb.support, is_well_formed (ca b)) :
    is_well_formed (bind cb ca)
| well_formed_rnd (A : Type) [inhabited A] [fintype A] :
    is_well_formed (rnd A)
| well_formed_repeat {A : Type} (p : A → Prop) [decidable_pred p] (ca : comp A) 
    (hca : is_well_formed ca) (hpca : (repeat p ca).support.nonempty) :
    is_well_formed (repeat p ca)

open is_well_formed

@[simp]
instance ret.is_well_formed {A : Type} (a : A) :
  (ret a).is_well_formed :=
well_formed_ret a

instance bind.is_well_formed {A B : Type} (cb : comp B) (ca : B → comp A)
  [hcb : cb.is_well_formed] [hca : ∀ b, (ca b).is_well_formed] :
  (cb.bind ca).is_well_formed :=
well_formed_bind cb ca hcb (λ b _, hca b)

@[simp]
instance rnd.is_well_formed {A : Type} [inhabited A] [fintype A] :
  (rnd A).is_well_formed :=
well_formed_rnd A

instance repeat.is_well_formed (p : A → Prop) [decidable_pred p]
  (ca : comp A) [hca : is_well_formed ca]
  (hpca : (repeat p ca).support.nonempty) :
  (ca.repeat p).is_well_formed :=
well_formed_repeat p ca hca hpca

@[simp] 
lemma is_well_formed_bind_iff (cb : comp B) (ca : B → comp A) :
  is_well_formed (cb.bind ca) ↔ 
    is_well_formed cb ∧ ∀ b ∈ cb.support, is_well_formed (ca b) :=
begin
  refine ⟨λ w, _, λ h, well_formed_bind cb ca h.1 h.2⟩,
  cases w,
  split; assumption,
end

@[simp]
lemma is_well_formed_bind_iff' (cb : comp B) (ca : B → comp A) :
  is_well_formed (cb >>= ca) ↔
    cb.is_well_formed ∧ ∀ b ∈ cb.support, (ca b).is_well_formed :=
is_well_formed_bind_iff cb ca

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
  induction hca with _ _ _ _ _ cb ca _ hcb_ih hca_ih A hA fA dA _ _ _ _ ha _,
  { simp },
  { obtain ⟨b, hb⟩ := hcb_ih,
    simp,
    refine ⟨b, hb, hca_ih b hb⟩ },
  { exact ⟨@arbitrary A hA, by simp⟩ },
  { exact ha },
end

end is_well_formed

end comp

