import computational_complexity.cost_model

/-!
# Computational Complexity Classes

This file defines the idea of a `complexity_class`, in terms of a `growth_pred` and a `cost_pred`.
The definition is fairly general so it can specialize to a variety of different possibilities.

The growth predicate can for example be polynomial, linear, polylogarithmic, etc.
The cost predicate can make this apply to `comp`, `oracle_comp`, or function evaluation.
It can also apply to both `≤` and `≥`, e.g. sub-polynomial or at-least-polynomial.
-/

/-- `complexity_class C growth_pred cost_pred c` means there is some `f` satisfying `growth_pred`
such that `c` and `f` jointly satisfy the cost predicate for all `n`. -/
def complexity_class {A B : Type*} (C : A → Type*) (growth_pred : (A → B) → Prop) 
  (cost_pred : Π (a : A), C a → B → Prop) (c : Π n, C n) :=
∃ (f : A → B), growth_pred f ∧ (∀ n, cost_pred n (c n) (f n))

namespace complexity_class 

variables {T : ℕ → Type} {A B C D : ℕ → Type*}

-- TODO: These have some higher structure, although generalizing might be messy

def poly_time_fun₁ (c : Π n, A n → B n) : Prop :=
complexity_class (λ n, A n → B n) poly_growth (λ n, has_cost) c

-- Instead maybe defintion should be that uncurried `c` is `poly_time_fun₁`
-- Not sure these are equiv, see partial proof below, this might be a weaker notion
def poly_time_fun₂ (c : Π n, A n → B n → C n) : Prop :=
poly_time_fun₁ c ∧ ∀ (a : Π n, A n), poly_time_fun₁ (λ n, c n (a n))

def poly_time_fun₃ (c : Π n, A n → B n → C n → D n) : Prop :=
poly_time_fun₁ c ∧ ∀ (a : Π n, A n), poly_time_fun₂ (λ n, c n (a n))

def poly_time_comp₀ (c : Π n, comp (T n)) : Prop :=
complexity_class (λ n, comp (T n)) poly_growth (λ n, comp_cost) c

def poly_time_comp₁ (c : Π n, A n → comp (T n)) : Prop :=
poly_time_fun₁ c ∧ ∀ (a : Π n, A n), poly_time_comp₀ (λ n, c n (a n))

def poly_time_comp₂ (c : Π n, A n → B n → comp (T n)) : Prop :=
poly_time_fun₁ c ∧ ∀ (a : Π n, A n), poly_time_comp₁ (λ n, c n (a n))

lemma poly_time_fun₂_iff_uncurry (c : Π n, A n → B n → C n) :
  poly_time_fun₂ c ↔ poly_time_fun₁ (λ n, function.uncurry (c n) : Π n, A n × B n → C n) :=
begin
  split; intro h,
  {
    obtain ⟨h, h'⟩ := h,
    let a : Π (n : ℕ), A n := sorry,
    specialize h' a,
    obtain ⟨p, hp, h⟩ := h,
    obtain ⟨q, hq, h'⟩ := h',
    refine ⟨p + q, poly_growth_add hp hq, _⟩,

    intro n,
    refine has_cost.has_cost_uncurry (h n) _,
    specialize h' n,
    simp at h' ⊢,
    sorry,
  },
  {
    obtain ⟨p, hp, h⟩ := h,
    refine ⟨⟨p, hp, λ n, has_cost.has_cost_of_uncurry (h n)⟩, 
      λ a, ⟨p, hp, λ n, has_cost.has_cost_of_uncurry' (a n) (h n)⟩⟩,
  }
end

-- lemma poly_time_cost_ext {A B : ℕ → Type} {c c' : Π n, A n → B n}
--   (hc : poly_time_cost c) (h : ∀ n a, c n a = c' n a) :
--   poly_time_cost c' :=
-- (funext (λ n, funext (λ a, h n a)) : c = c') ▸ hc

end complexity_class