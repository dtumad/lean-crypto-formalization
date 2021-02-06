import data.bitvec.basic

/-- Computational monad to extend the base language of Lean for cryptography purposes.
  `Rnd n` represents a computation of purely random bits, 
  and `Repeat` can repeat a random computation until some predicate holds -/
inductive Comp : Type → Sort*
| Ret {A : Type} [hA : decidable_eq A] : Π (a : A), Comp A
| Bind {A B : Type} : Π (cb : Comp B) (ca : B → Comp A), Comp A
| Rnd : ∀ (n : ℕ), Comp (bitvec n)
| Repeat {A : Type} : Π (p : A → Prop) [decidable_pred p] (ca : Comp A) , Comp A

namespace Comp
open Comp

variables {A B : Type}

/-- Every computation non-constructively gives an element of the return type-/
def comp_base_exists (ca : Comp A) : A :=
@Comp.rec_on (λ A _, A) A ca
  (λ _ _ a, a) (λ _ _ _ _ b fa, fa b)
  (λ n, vector.repeat tt n) (λ _ _ _ _ a, a)

/-- Because only `Ret` and `Rnd` terminate computation, and `Ret` requires `decidable_eq A`,
  every computation must return a type with decidable equality.
  This needs to be definitional to make `support` fully computable -/
def decidable_eq_of_Comp (ca : Comp A) : decidable_eq A :=
@Comp.rec_on (λ A _, decidable_eq A) A ca
  (λ _ h _, h) (λ A B cb ca hcb hca, hca cb.comp_base_exists)
  (λ _, (by apply_instance)) (λ _ _ _ _ h, h)

/-- alias because this situation is very common due to use of `bUnion` in support -/
def decidable_eq_of_Comp' (cb : Comp B) (ca : B → Comp A) : decidable_eq A :=
Comp.decidable_eq_of_Comp $ Bind cb ca


section support

/-- The support of `Comp A` is a list of elements of `A` with non-zero probability of being computed -/
def support (ca : Comp A) : finset A :=
ca.rec_on (λ _ _ a, {a}) 
  (λ A B cb ca hcb hca, @finset.bUnion B A (decidable_eq_of_Comp' cb ca) hcb hca)
  (λ _, finset.univ) (λ _ p hp _, @finset.filter _ p hp)

@[simp] lemma support_Ret [decidable_eq A] (a : A) :
  (Ret a).support = {a} := rfl

@[simp] lemma mem_support_Ret_iff [decidable_eq A] (a a' : A) : 
  a ∈ (Ret a').support ↔ a = a' := by simp

@[simp] lemma support_Bind (cb : Comp B) (ca : B → Comp A) :
  (Bind cb ca).support = @finset.bUnion B A (decidable_eq_of_Comp' cb ca) 
    cb.support (λ b, (ca b).support) := rfl

@[simp] lemma mem_support_Bind_iff (cb : Comp B) (ca : B → Comp A) (a : A) :
  a ∈ (Comp.Bind cb ca).support ↔ ∃ (b : B), b ∈ cb.support ∧ a ∈ (ca b).support := by simp

@[simp] lemma support_Rnd {n : ℕ} : (Rnd n).support = finset.univ := rfl

lemma mem_support_Rnd {n : ℕ} (b : bitvec n) : 
  b ∈ (Rnd n).support := by simp

@[simp] lemma support_Repeat (ca : Comp A) (p : A → Prop) [decidable_pred p] :
  (Repeat p ca).support = ca.support.filter p := rfl

@[simp] lemma mem_support_Repeat (ca : Comp A) (p : A → Prop) [decidable_pred p] (a : A) :
  a ∈ (Repeat p ca).support ↔ a ∈ ca.support ∧ p a = tt := by simp

end support


section well_formed_Comp 

/-- A computation is well formed if both of the following conditions hold:
  1 - All sub-computations are well-formed (Trivial for `Ret` and `Rnd`)
  2 - The computation has non-empty support (Trivial for all but `Repeat`)
  Such a computation is gaurunteed to have a non-empty support -/
inductive well_formed_Comp : ∀ {A : Type}, Comp A → Prop
| well_formed_Ret {A : Type} [hA : decidable_eq A] (a : A) :
    well_formed_Comp (@Ret A hA a)
| well_formed_Bind {A B : Type} (cb : Comp B) (ca : B → Comp A) 
    (hcb : well_formed_Comp cb) 
    (hca : ∀ b ∈ cb.support, well_formed_Comp (ca b)) :
    well_formed_Comp (Bind cb ca)
| well_formed_Rnd {n : ℕ} :
    well_formed_Comp (Rnd n)
| well_formed_Repeat {A : Type} (p : A → Prop) [decidable_pred p] (ca : Comp A) 
    (hca : well_formed_Comp ca) (hpca : (Repeat p ca).support.nonempty) :
    well_formed_Comp (Repeat p ca)

open well_formed_Comp

theorem support_nonempty_of_well_formed_Comp (ca : Comp A)
  (hca : well_formed_Comp ca) : ca.support.nonempty :=
begin
  induction hca with _ _ _ _ _ cb ca _ _ hcb_ih hca_ih n _ _ _ _ _ ha _,
  { simp },
  { obtain ⟨b, hb⟩ := hcb_ih,
    obtain ⟨a, ha⟩ := hca_ih b hb,
    exact ⟨a, (mem_support_Bind_iff cb ca a).2 ⟨b, hb, ha⟩⟩ },
  { exact ⟨(Rnd n).comp_base_exists, mem_support_Rnd _⟩ },
  { exact ha },
end

end well_formed_Comp


section oracle_Comp

inductive oracle_Comp : Type → Type → Type → Sort*
| oc_query {A B : Type} : Π (a : A), oracle_Comp A B B
| oc_ret {A B C : Type} : Π (c : C), oracle_Comp A B C
| oc_bind {A B C D : Type} : Π (oc : oracle_Comp A B C) (od : C → oracle_Comp A B D),
    oracle_Comp A B D
| oc_run {A B C A' B' S : Type} [decidable_eq A] [decidable_eq B] [decidable_eq S] :
    Π (oc : oracle_Comp A B C) (ob : S → A → oracle_Comp A' B' (B × S)) (s : S), 
      oracle_Comp A' B' (C × S)

end oracle_Comp

end Comp

