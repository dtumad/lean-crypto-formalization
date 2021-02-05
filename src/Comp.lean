import data.bitvec.basic
import tactic.induction

inductive Comp : Type → Sort*
| Ret {A : Type} [hA : decidable_eq A] : Π (a : A), Comp A
| Bind {A B : Type} : Π (cb : Comp B) (ca : B → Comp A), Comp A
| Rnd : ∀ (n : ℕ), Comp (bitvec n)
| Repeat {A : Type} : Π (p : A → Prop) [decidable_pred p] (ca : Comp A) , Comp A


namespace Comp
open Comp

variables {A B : Type}

def comp_base_exists (ca : Comp A) : A :=
@Comp.rec_on (λ A _, A) A ca
  (λ _ _ a, a) (λ _ _ _ _ b fa, fa b)
  (λ n, vector.repeat tt n) (λ _ _ _ _ a, a)

def decidable_eq_of_Comp (ca : Comp A) : decidable_eq A :=
@Comp.rec_on (λ A _, decidable_eq A) A ca
  (λ _ h _, h) (λ A B cb ca hcb hca, hca cb.comp_base_exists)
  (λ _, (by apply_instance)) (λ _ _ _ _ h, h)

def decidable_eq_of_Comp' (cb : Comp B) (ca : B → Comp A) : decidable_eq A :=
Comp.decidable_eq_of_Comp $ ca cb.comp_base_exists


section support

-- The support of `Comp A` is a list of elements of `A` with non-zero probability of being computed
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

inductive well_formed_Comp : ∀ {A : Type}, Comp A → Prop
| well_formed_Ret {A : Type} [hA : decidable_eq A] (a : A) :
    well_formed_Comp (@Ret A hA a)
| well_formed_Bind {A B : Type} (cb : Comp B) (ca : B → Comp A) 
    (hcb : well_formed_Comp cb) 
    (hca : ∀ b ∈ cb.support, well_formed_Comp (ca b)) :
    well_formed_Comp (Bind cb ca)
| well_formed_Rnd {n : ℕ} :
    well_formed_Comp (Rnd n)
| well_formed_Repeat {A : Type} (ca : Comp A) (p : A → Prop) [decidable_pred p] (a : A)
    (hca : well_formed_Comp ca) (ha : a ∈ (Repeat p ca).support) :
    well_formed_Comp (Repeat p ca)

theorem support_nonempty_of_well_formed_Comp (ca : Comp A)
  (hca : well_formed_Comp ca) : ca.support.nonempty :=
begin
  induction hca with _ _ _ _ _ cb ca _ _ hcb_ih hca_ih n _ _ _ _ a _ ha _,
  { simp },
  { obtain ⟨b, hb⟩ := hcb_ih,
    obtain ⟨a, ha⟩ := hca_ih b hb,
    exact ⟨a, (mem_support_Bind_iff cb ca a).2 ⟨b, hb, ha⟩⟩ },
  { exact ⟨(Rnd n).comp_base_exists, mem_support_Rnd _⟩ },
  { exact ⟨a, ha⟩ },
end

end well_formed_Comp

end Comp

