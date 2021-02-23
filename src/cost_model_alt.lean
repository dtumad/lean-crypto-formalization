import comp
import to_mathlib

universes u v w

-- #check (↑ℕ : Type 2)

/-- We define -/
structure function_cost_model :=
(has_cost {A : Type} {B : Type 1} : (A → B) → ℕ → Prop)
(has_cost_le {A : Type} {B : Type 1} {f : A → B} {n m : ℕ} (hnm : n ≤ m) : has_cost f n → has_cost f m)
-- (has_cost_compose {A : Type u} {B : Type v} {C : Type w} {f : A → B} {g : A → B → C} {n1 n2 n3 : ℕ} :
--   has_cost f n1 → @has_cost A (B → C) g n2 → (∀ a, has_cost (g a) n3) → has_cost (λ a, g a (f a)) (n1 + n2 + n3))

-- axiom has_cost_compose' {A B C : Type*} {f : A → B} {g : A → B → C} {n1 n2 n3 : ℕ} :
--     has_cost f n1 → has_cost g n2 → (∀ a, has_cost (g a) n3) → has_cost (λ a, g a (f a)) (n1 + n2 + n3)

-- axiom has_cost_uncurry {A B C : Type*} {f : A → B → C} {n1 n2 : ℕ} :
--     has_cost f n1 → (∀ a, has_cost (f a) n2) → has_cost (function.uncurry f) (n1 + n2)

-- axiom has_cost_curry {A B C : Type*} {f : A → B → C} {n : ℕ} :
--     has_cost (function.uncurry f) n → has_cost f n

-- axiom has_cost_curry' {A B C : Type*} {f : A → B → C} {n : ℕ} {a : A} :
--     has_cost (function.uncurry f) n → has_cost (f a) n

/-- Defines an extensible axiomatic cost model for Lean functions -/
constant cm : function_cost_model

axiom has_cost_ret {A : Type} [decidable_eq A] :
  @function_cost_model.has_cost cm A (Comp A) (Comp.ret : A → Comp A) 0

axiom cm_id {A : Type*} : 
  @function_cost_model.has_cost cm A A (id : A → A) 0

axiom cm_const {A B : Type*} (b : B) : cm.has_cost (λ _, b : A → B) 0

axiom has_cost_compose {A : Type u} {B : Type v} {C : Type w} {f : A → B} {g : A → B → C} {n1 n2 n3 : ℕ} :
  cm.has_cost f n1 → cm.has_cost g n2 → (∀ a, cm.has_cost (g a) n3) → cm.has_cost (λ a, g a (f a)) (n1 + n2 + n3)


lemma has_cost_comp {A B C : Type*} {f : A → B} {g : B → C} {n m : ℕ} 
  (hf : cm.has_cost f n) (hg : cm.has_cost g m) : 
  cm.has_cost (g ∘ f) (n + m) :=
begin
  have := has_cost_compose hf (cm_const _) (λ a, hg),
  simpa using this,
end



def comp_cost_model := ∀ {A : Type*}, Comp A → ℕ → Prop

inductive comp_cost (fm : function_cost_model) : comp_cost_model
| cost_ret {A : Type} [decidable_eq A] {a : A} :
    comp_cost (Comp.ret a) 0
| cost_bind {A B : Type} {ca : Comp A} {cb : A → Comp B} {n1 n2 n3 : ℕ} :
    comp_cost ca n1 → fm.has_cost cb n2 → (∀ a, comp_cost (cb a) n3) → comp_cost (Comp.bind ca cb) (n1 + n2 + n3)
