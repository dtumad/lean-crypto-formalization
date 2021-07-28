import computational_complexity.cost_model

/-!
# Computational Complexity Classes

This file defines the idea of a `complexity_class`, in terms of a `growth_pred` and a `cost_pred`.
The definition is fairly general so it can specialize to a variety of different possibilities.

The growth predicate can for example be polynomial, linear, polylogarithmic, etc.
The cost predicate can make this apply to `comp`, `oracle_comp`, or function evaluation.
It can also apply to both `≤` and `≥`, e.g. sub-polynomial or at-least-polynomial.

-- TODO: Do this with oracle_comp, but also require a polynomial number of queries
-/

universes u v w

-- TODO: maybe just have `polynomial_time` and `prob_polynomial_time`?

namespace complexity_class 

open cost_model

-- TODO: Try working with a more general definition like this?
def polynomial_complexity {A : ℕ → Type u} [∀ n, cost_model ℚ (A n)]
  (c : Π n, A n) : Prop :=
∃ (f : ℕ → ℚ), poly_growth f ∧ ∀ n, cost_at_most (c n) (f n)




section poly_time_fun

/-- `poly_time_fun c` means `c` can be evaluated in polynomial time on any input -/
def poly_time_fun {A B : ℕ → Type u} [function_cost_model.{u} ℚ]
  (c : Π n, A n → B n) : Prop :=
∃ (f : ℕ → ℚ), poly_growth f ∧ ∀ n, cost_at_most (c n) (f n)

variables  {A B C D : ℕ → Type u}

section poly_growth_const

lemma poly_time_fun_of_has_cost_const [function_cost_model.{u} ℚ] {A B : ℕ → Type u} {c : Π n, A n → B n} (x : ℚ)
  (hn : ∀ n, cost_at_most (c n) x) : poly_time_fun c :=
⟨λ n, x, poly_growth_const x, hn⟩

@[simp]
lemma poly_time_fun_const [function_cost_model.{u} ℚ] (A : ℕ → Type u) {B : ℕ → Type u} (b : Π (n : ℕ), B n) :
  poly_time_fun (λ n, (λ _, b n : A n → B n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, by simp)

@[simp]
lemma poly_time_fun_fst [pairing_cost_model.{u} ℚ] (A B : ℕ → Type u) :
  poly_time_fun (λ n, (prod.fst : A n × B n → A n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, by simp)

@[simp]
lemma poly_time_fun_snd [pairing_cost_model.{u} ℚ] (A B : ℕ → Type u) :
  poly_time_fun (λ n, (prod.snd : A n × B n → B n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, by simp)

end poly_growth_const

variable [pairing_cost_model.{u} ℚ]

lemma poly_time_fun_comp {c : Π n, A n → B n} {d : Π n, B n → C n}
  (hc : poly_time_fun c) (hd : poly_time_fun d) :
  poly_time_fun (λ n, d n ∘ c n) :=
let ⟨p, hp, hpc⟩ := hc in let ⟨q, hq, hqd⟩ := hd in
⟨p + q, poly_growth_add hp hq, λ n, 
  compatible_cost_models.cost_at_most_compose_of_le (hpc n) (hqd n) (by simp)⟩

lemma poly_time_fun_comp_ext {c : Π n, A n → B n} {d : Π n, B n → C n} {e : Π n, A n → C n}
  (hc : poly_time_fun c) (hd : poly_time_fun d) (he : ∀ n a, e n a = d n (c n a)) :
  poly_time_fun e :=
(funext $ λ n, funext $ λ a, (he n a).symm : (λ n, d n ∘ c n) = e)
  ▸ poly_time_fun_comp hc hd

-- @[simp]
-- lemma poly_time_fun_pair_iff [∀ n, inhabited $ A n] [∀ n, inhabited $ C n]
--   (c : Π n, A n → B n) (d : Π n, C n → D n) :
--   poly_time_fun (λ n, (λ x, (c n x.1, d n x.2) : A n × C n → B n × D n)) ↔
--     poly_time_fun c ∧ poly_time_fun d :=
-- begin
--   sorry
--   -- refine ⟨_, _⟩,
--   -- { rintro ⟨p, hp, h⟩,
--   --   exact ⟨⟨p, hp, λ n, has_cost.has_cost_of_prod $ h n⟩,
--   --     ⟨p, hp, λ n, has_cost.has_cost_of_prod' $ h n⟩⟩ },
--   -- { rintro ⟨⟨p, hp, h⟩, ⟨q, hq, h'⟩⟩,
--   --   refine ⟨p + q, poly_growth_add hp hq, λ n, _⟩,
--   --   simpa using has_cost.has_cost_prod (h n) (h' n) }
-- end

end poly_time_fun

section poly_time_comp

variables [function_cost_model.{0} ℚ] --[function_cost_model.{1} ℚ]
variable [comp_cost_model ℚ]

-- def poly_time_comp₀ {T : ℕ → Type} (c : Π n, comp (T n)) : Prop :=
-- ∃ (p : ℕ → ℚ), poly_growth p ∧ ∀ n, cost_at_most (c n) (p n)

/-- `poly_time_comp₁ c` means evaluating `c : A n → comp (T n)` at any `a : A n`,
  and then sampling from the result has polynomial time cost in `n`.
  todo: Essentially non-uniform probabalistic polynomial time -/
def poly_time_comp₁ {A : ℕ → Type} {T : ℕ → Type} (c : Π n, A n → comp (T n)) : Prop :=
∃ (p : ℕ → ℚ), poly_growth p ∧ ∀ n, (cost_at_most (c n) (p n))

-- lemma poly_time_comp₁_ret_of_poly_time_fun {A B : ℕ → Type} 
--   (f : Π n, A n → B n) (hf : poly_time_fun.{0} f) :
--   poly_time_comp₁ (λ n, (λ a, comp.ret (f n a))) :=
-- begin
--   obtain ⟨p, hp, h⟩ := hf, sorry,
-- end

-- lemma poly_time_comp₁_bind_of_poly_time_fun_uncurry {T U V : ℕ → Type}
--   (cu : Π n, T n → comp (U n)) (hcu : poly_time_comp₁ cu)
--   (cv : Π n, T n → U n → comp (V n)) 
--   (hcv : poly_time_comp₁ (λ n, (function.uncurry (cv n) : (T n × U n) → comp (V n)))) :
--   poly_time_comp₁ (λ n, (λ t, comp.bind (cu n t) (cv n t))) :=
-- sorry

end poly_time_comp

end complexity_class