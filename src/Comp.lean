import data.bitvec.basic
import tactic.induction
import tactic.local_cache
import to_mathlib


universes u v


/-- Computational monad to extend the base language of Lean for cryptography purposes.
  `rnd n` represents a computation of purely random bits, 
  and `repeat` can repeat a random computation until some predicate holds -/
inductive Comp : Π (A : Type), Type 1
| ret {A : Type} [hA : decidable_eq A] : Π (a : A), Comp A
| bind {A B : Type} : Π (cb : Comp B) (ca : B → Comp A), Comp A
| rnd : Π (n : ℕ), Comp (bitvec n)
| repeat {A : Type} : Π (p : A → Prop) [decidable_pred p] (ca : Comp A) , Comp A

namespace Comp
open Comp


variables {A B C : Type}

/-- Every computation gives rise to at least one element of the return type, 
  in particular this is the result if all `rnd` calls return strings of `1` bits. -/
def comp_base_exists (ca : Comp A) : A :=
@Comp.rec_on (λ A _, A) A ca
  (λ A hA a, a) (λ A B cb ca b fa, fa b)
  (λ n, vector.repeat tt n) (λ A p hp ca a, a)

/-- Because only `ret` and `rnd` terminate computation, and `ret` requires `decidable_eq A`,
  every computation must return a type with decidable equality.
  This needs to be definitional to make `support` fully computable -/
def decidable_eq_of_Comp (ca : Comp A) : decidable_eq A :=
@Comp.rec_on (λ A _, decidable_eq A) A ca
  (λ A hA a, hA) (λ A B cb ca hcb hca, hca cb.comp_base_exists)
  (λ n, (by apply_instance)) (λ A p hp ca h, h)

/-- alias because this situation is very common due to use of `bUnion` in support -/
def decidable_eq_of_Comp' (cb : Comp B) (ca : B → Comp A) : decidable_eq A :=
Comp.decidable_eq_of_Comp $ bind cb ca


section support

/-- The support of `Comp A` is the elements of `A` with non-zero probability of being computed -/
def support (ca : Comp A) : finset A :=
ca.rec (λ _ _ a, {a}) 
  (λ A B cb ca hcb hca, @finset.bUnion B A (decidable_eq_of_Comp' cb ca) hcb hca)
  (λ n, finset.univ) (λ A p hp ca, @finset.filter _ p hp)

@[simp] lemma support_ret [decidable_eq A] (a : A) :
  (ret a).support = {a} := rfl

@[simp] lemma mem_support_ret_iff [decidable_eq A] (a a' : A) : 
  a ∈ (ret a').support ↔ a = a' := by simp

@[simp] lemma support_bind (cb : Comp B) (ca : B → Comp A) :
  (bind cb ca).support = @finset.bUnion B A (decidable_eq_of_Comp' cb ca) 
    cb.support (λ b, (ca b).support) := rfl

@[simp] lemma mem_support_bind_iff (cb : Comp B) (ca : B → Comp A) (a : A) :
  a ∈ (Comp.bind cb ca).support ↔ ∃ (b : B), b ∈ cb.support ∧ a ∈ (ca b).support := by simp

@[simp] lemma support_rnd {n : ℕ} : (rnd n).support = finset.univ := rfl

@[simp] lemma mem_support_rnd {n : ℕ} (b : bitvec n) : 
  b ∈ (rnd n).support := by simp

@[simp] lemma support_repeat (ca : Comp A) (p : A → Prop) [decidable_pred p] :
  (repeat p ca).support = ca.support.filter p := rfl

@[simp] lemma mem_support_repeat (ca : Comp A) (p : A → Prop) [decidable_pred p] (a : A) :
  a ∈ (repeat p ca).support ↔ a ∈ ca.support ∧ p a := by simp

end support


section well_formed_Comp 

/-- A computation is well formed if both of the following conditions hold:
  1 - All sub-computations are well-formed (Trivial for `ret` and `rnd`)
  2 - The computation has non-empty support (Trivial for all but `repeat`)
  Such a computation is gaurunteed to have a non-empty support -/
inductive well_formed_Comp : ∀ {A : Type}, Comp A → Prop
| well_formed_ret {A : Type} [hA : decidable_eq A] (a : A) :
    well_formed_Comp (@ret A hA a)
| well_formed_bind {A B : Type} (cb : Comp B) (ca : B → Comp A) 
    (hcb : well_formed_Comp cb) 
    (hca : ∀ b ∈ cb.support, well_formed_Comp (ca b)) :
    well_formed_Comp (bind cb ca)
| well_formed_rnd {n : ℕ} :
    well_formed_Comp (rnd n)
| well_formed_repeat {A : Type} (p : A → Prop) [decidable_pred p] (ca : Comp A) 
    (hca : well_formed_Comp ca) (hpca : (repeat p ca).support.nonempty) :
    well_formed_Comp (repeat p ca)

open well_formed_Comp

@[simp] lemma well_formed_Comp_ret [decidable_eq A] (a : A) : well_formed_Comp (ret a) :=
well_formed_ret a

@[simp] lemma well_formed_Comp_bind_iff (cb : Comp B) (ca : B → Comp A) :
  well_formed_Comp (cb.bind ca) ↔ 
    well_formed_Comp cb ∧ ∀ b ∈ cb.support, well_formed_Comp (ca b) :=
begin
  refine ⟨λ w, _, λ h, well_formed_bind cb ca h.1 h.2⟩,
  cases w,
  split; assumption,
end

@[simp] lemma well_formed_Comp_rnd (n : ℕ) : well_formed_Comp (rnd n) :=
well_formed_rnd

@[simp] lemma well_formed_Comp_repeat_iff (p : A → Prop) [hp : decidable_pred p] (ca : Comp A) :
  well_formed_Comp (@repeat A p hp ca) ↔ well_formed_Comp ca ∧ (repeat p ca).support.nonempty :=
begin
  refine ⟨λ w, _, λ h, well_formed_repeat p ca h.1 h.2⟩,
  tactic.unfreeze_local_instances,
  cases w,
  split; assumption,
end

theorem support_nonempty_of_well_formed_Comp (ca : Comp A)
  (hca : well_formed_Comp ca) : ca.support.nonempty :=
begin
  induction hca with _ _ _ _ _ cb ca _ _ hcb_ih hca_ih n _ _ _ _ _ ha _,
  { simp },
  { obtain ⟨b, hb⟩ := hcb_ih,
    obtain ⟨a, ha⟩ := hca_ih b hb,
    exact ⟨a, (mem_support_bind_iff cb ca a).2 ⟨b, hb, ha⟩⟩ },
  { exact ⟨(rnd n).comp_base_exists, mem_support_rnd _⟩ },
  { exact ha },
end

end well_formed_Comp


section Oracle_Comp

/-- `Oracle_Comp A B C` is the type of a computation of a value of type `C`,
  with access to an oracle taking values in `A` to values in `B`.
  `oc_run` represents computing `oc` with `ob` as a proxy for the oracle -/
inductive Oracle_Comp : Type → Type → Type → Type 1
| oc_query {A B : Type} : Π (a : A), Oracle_Comp A B B
| oc_ret {A B C : Type} : Π (c : Comp C), Oracle_Comp A B C
| oc_bind {A B C D : Type} : Π (oc : Oracle_Comp A B C) (od : C → Oracle_Comp A B D),
    Oracle_Comp A B D
| oc_run {A B C A' B' S : Type} [decidable_eq A] [decidable_eq B] [decidable_eq S] :
    Π (oc : Oracle_Comp A B C) (ob : S → A → Oracle_Comp A' B' (B × S)) (s : S), 
      Oracle_Comp A' B' (C × S)

/-- Every oracle_comp gives rise to a mapping from query assignments to the base comp type,
  where the value in `C` is the result of the computation if oracles behave like the input -/
def oracle_comp_base_exists (oc : Oracle_Comp A B C) : (A → B) → C :=
@Oracle_Comp.rec_on (λ A B C _, (A → B) → C) A B C oc
  (λ A B a q, q a) (λ A B C cc hcc, cc.comp_base_exists)
  (λ A B C D oc od hoc hod q, hod (hoc q) q)
  (λ A B C A' B' S hA hB hS oc ob s hoc hob q, ⟨hoc (λ a, (hob s a q).1), s⟩)

def decidable_eq_of_oracle_comp (oc : Oracle_Comp A B C) : 
  (A → B) → (A → decidable_eq B) → decidable_eq C :=
@Oracle_Comp.rec_on (λ A B C _, (A → B) → (A → decidable_eq B) → decidable_eq C) 
  A B C oc (λ A B a t h, h a) 
  (λ A B C cc tcc hcc, decidable_eq_of_Comp cc) 
  (λ A B C D oc od hoc hod t h, hod (oracle_comp_base_exists oc t) t h)
  (λ A B C A' B' S hA hB hS oc ob s hoc hob t h, @prod.decidable_eq C S 
    (hoc (λ a, (oracle_comp_base_exists (ob s a) t).1) 
      (λ a, @decidable_eq_of_prod_left B S (hob s a t h) s)) hS)

end Oracle_Comp

end Comp

