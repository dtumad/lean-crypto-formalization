import data.list
import init.meta.mk_dec_eq_instance
import data.bitvec.basic

lemma test {A B : Type*} : (A = B) → A → B :=
begin
  intro h,
  exact eq.rec_on h id,
end

set_option trace.check true

universes u v

inductive Comp : Type* → Sort*
| Ret {A : Type*} [decidable_eq A] : Π (a : A), Comp A
| Bind {A B : Type*} : Π (cb : Comp B) (ca : B → Comp A), Comp A
| Rnd : ∀ (n : ℕ), Comp (bitvec n)
| Repeat {A : Type*} : Π (ca : Comp A) (p : A → bool), Comp A

open Comp

lemma comp_base_exists {A : Type*} : Comp A → A :=
λ ca, @Comp.rec_on (λ A _, A) A ca 
  (λ _ _ a, a) (λ _ _ _ _ b fa, fa b)
  (λ n, vector.repeat tt n) (λ _ _ _ a, a)

theorem decidable_eq_of_Comp {A : Type*} : Comp A → decidable_eq A :=
λ ca, @Comp.rec_on (λ A _, decidable_eq A) A ca
  (λ _ h _, h) (λ A B cb ca hcb hca, hca (comp_base_exists cb))
  (λ _, (by apply_instance)) (λ _ _ _ h, h)

