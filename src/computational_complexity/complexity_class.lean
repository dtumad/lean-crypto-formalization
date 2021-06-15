import computational_complexity.cost_model

/-!
# Computational Complexity Classes

This file defines the idea of a `complexity_class`, in terms of a `growth_pred` and a `cost_pred`.
The definition is fairly general so it can specialize to a variety of different possibilities.

The growth predicate can for example be polynomial, linear, polylogarithmic, etc.
The cost predicate can make this apply to `comp`, `oracle_comp`, or function evaluation.
It can also apply to both `≤` and `≥`, e.g. sub-polynomial or at-least-polynomial.
-/

section complexity_class

/-- `complexity_class C growth_pred cost_pred c` means there is some `f` satisfying `growth_pred`
such that `c` and `f` jointly satisfy the cost predicate for all `n`. -/
def complexity_class {A B : Type*} (C : A → Type*) (growth_pred : (A → B) → Prop) 
  (cost_pred : Π (a : A), C a → B → Prop) (c : Π n, C n) :=
∃ (f : A → B), growth_pred f ∧ (∀ n, cost_pred n (c n) (f n))

def poly_time_cost {A B : ℕ → Type*} (c : Π n, A n → B n) :=
complexity_class (λ n, A n → B n) poly_growth (λ n, has_cost) c

@[simp] lemma poly_time_cost_def {A B : ℕ → Type*} (c : Π n, A n → B n) :
  poly_time_cost c ↔ ∃ (f : ℕ → ℚ), poly_growth f ∧ (∀ n, has_cost (c n) (f n)) :=
iff.rfl

def poly_time_comp {A : ℕ → Type} (c : Π n, comp (A n)) :=
complexity_class (λ n, comp (A n)) poly_growth (λ n, comp_cost) c

@[simp] lemma poly_time_comp_iff {A : ℕ → Type} (c : Π n, comp (A n)) :
  poly_time_comp c ↔ ∃ (f : ℕ → ℚ), poly_growth f ∧ (∀ n, comp_cost (c n) (f n)) :=
iff.rfl

lemma poly_time_cost_ext {A B : ℕ → Type} {c c' : Π n, A n → B n}
  (hc : poly_time_cost c) (h : ∀ n a, c n a = c' n a) :
  poly_time_cost c' :=
(funext (λ n, funext (λ a, h n a)) : c = c') ▸ hc

end complexity_class