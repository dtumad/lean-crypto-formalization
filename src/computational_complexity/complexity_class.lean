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

-- TODO: compare these two possible defintions.
-- Current one gives the nice uncurry connection down below
def poly_time_fun₂ (c : Π n, A n → B n → C n) : Prop :=
--poly_time_fun₁ c ∧ ∀ (a : Π n, A n), poly_time_fun₁ (λ n, c n (a n))
complexity_class (λ n, A n → B n → C n) poly_growth (λ n c x, has_cost c x ∧ ∀ a, has_cost (c a) x) c

def poly_time_fun₃ (c : Π n, A n → B n → C n → D n) : Prop :=
poly_time_fun₁ c ∧ ∀ (a : Π n, A n), poly_time_fun₂ (λ n, c n (a n))

def poly_time_comp₀ (c : Π n, comp (T n)) : Prop :=
complexity_class (λ n, comp (T n)) poly_growth (λ n, comp_cost) c

def poly_time_comp₁ (c : Π n, A n → comp (T n)) : Prop :=
poly_time_fun₁ c ∧ ∀ (a : Π n, A n), poly_time_comp₀ (λ n, c n (a n))

def poly_time_comp₂ (c : Π n, A n → B n → comp (T n)) : Prop :=
poly_time_fun₁ c ∧ ∀ (a : Π n, A n), poly_time_comp₁ (λ n, c n (a n))

lemma poly_time_fun₁_comp (c : Π n, A n → B n) (d : Π n, B n → C n)
  (hc : poly_time_fun₁ c) (hd : poly_time_fun₁ d) :
  poly_time_fun₁ (λ n, d n ∘ c n) :=
let ⟨p, hp, hpc⟩ := hc in let ⟨q, hq, hqd⟩ := hd in
⟨p + q, poly_growth_add hp hq, λ n, has_cost.has_cost_comp (hpc n) (hqd n)⟩

lemma poly_time_fun₂_iff_uncurry (c : Π n, A n → B n → C n) :
  poly_time_fun₂ c ↔ poly_time_fun₁ (λ n, function.uncurry (c n) : Π n, A n × B n → C n) :=
begin
  split; intro h,
  {
    obtain ⟨p, hp, hpc⟩ := h,
    refine ⟨p + p, poly_growth_add hp hp, λ n, _⟩,
    specialize hpc n,
    refine has_cost.has_cost_uncurry hpc.1 hpc.2,
  },
  { obtain ⟨p, hp, hpc⟩ := h,
    refine ⟨p, hp, λ n, _⟩,
    specialize hpc n,
    refine ⟨has_cost.has_cost_of_uncurry hpc, _⟩,
    exact λ a, has_cost.has_cost_of_uncurry' a hpc,
  }
end

end complexity_class