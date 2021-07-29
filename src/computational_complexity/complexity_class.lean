import computational_complexity.cost_model

/-!
# Computational Complexity Classes

This file defines the idea of a `complexity_class`, in terms of a `growth_pred` and a `cost_pred`.
The definition is fairly general so it can specialize to a variety of different possibilities.

The growth predicate can for example be polynomial, linear, polylogarithmic, etc.
The cost predicate can make this apply to `comp`, `oracle_comp`, or function evaluation.
It can also apply to both `≤` and `≥`, e.g. sub-polynomial or at-least-polynomial.

-/

universes u v

namespace complexity_class 

open cost_model

def polynomial_complexity {A : ℕ → Type u} [∀ n, cost_model ℚ (A n)]
  (c : Π n, A n) : Prop :=
∃ (f : ℕ → ℚ), poly_growth f ∧ ∀ n, cost_at_most (c n) (f n)

variables  {A B C D : ℕ → Type}

lemma polynomial_complexity_of_has_cost_const [function_cost_model ℚ] {c : Π n, A n → B n} (x : ℚ)
  (hn : ∀ n, cost_at_most (c n) x) : polynomial_complexity c :=
⟨λ n, x, poly_growth_const x, hn⟩

section poly_growth_const

@[simp]
lemma polynomial_complexity_const [function_cost_model ℚ] (A : ℕ → Type) (b : Π (n : ℕ), B n) :
  polynomial_complexity (λ n, (λ _, b n : A n → B n)) :=
polynomial_complexity_of_has_cost_const 0 (λ n, by simp)

@[simp]
lemma polynomial_complexity_fst [pairing_cost_model ℚ] (A B : ℕ → Type) :
  polynomial_complexity (λ n, (prod.fst : A n × B n → A n)) :=
polynomial_complexity_of_has_cost_const 0 (λ n, by simp)

@[simp]
lemma polynomial_complexity_snd [pairing_cost_model ℚ] (A B : ℕ → Type) :
  polynomial_complexity (λ n, (prod.snd : A n × B n → B n)) :=
polynomial_complexity_of_has_cost_const 0 (λ n, by simp)

end poly_growth_const

variable [pairing_cost_model ℚ]

lemma polynomial_complexity_comp {c : Π n, A n → B n} {d : Π n, B n → C n}
  (hc : polynomial_complexity c) (hd : polynomial_complexity d) :
  polynomial_complexity (λ n, d n ∘ c n : Π n, A n → C n) :=
let ⟨p, hp, hpc⟩ := hc in let ⟨q, hq, hqd⟩ := hd in
⟨p + q, poly_growth_add hp hq, λ n, 
  compatible_cost_models.cost_at_most_compose_of_le (hpc n) (hqd n) (by simp)⟩

lemma polynomial_complexity_comp_ext {c : Π n, A n → B n} {d : Π n, B n → C n} {e : Π n, A n → C n}
  (hc : polynomial_complexity c) (hd : polynomial_complexity d) (he : ∀ n a, e n a = d n (c n a)) :
  polynomial_complexity e :=
(funext $ λ n, funext $ λ a, (he n a).symm : (λ n, d n ∘ c n) = e)
  ▸ polynomial_complexity_comp hc hd

-- @[simp]
-- lemma polynomial_complexity_pair_iff [∀ n, inhabited $ A n] [∀ n, inhabited $ C n]
--   (c : Π n, A n → B n) (d : Π n, C n → D n) :
--   polynomial_complexity (λ n, (λ x, (c n x.1, d n x.2) : A n × C n → B n × D n)) ↔
--     polynomial_complexity c ∧ polynomial_complexity d :=
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

-- lemma polynomial_complexity_ret_of_polynomial_complexity {A B : ℕ → Type} 
--   (f : Π n, A n → B n) (hf : polynomial_complexity.{0} f) :
--   polynomial_complexity (λ n, (λ a, comp.ret (f n a))) :=
-- begin
--   obtain ⟨p, hp, h⟩ := hf, sorry,
-- end

-- lemma polynomial_complexity_bind_of_polynomial_complexity_uncurry {T U V : ℕ → Type}
--   (cu : Π n, T n → comp (U n)) (hcu : polynomial_complexity cu)
--   (cv : Π n, T n → U n → comp (V n)) 
--   (hcv : polynomial_complexity (λ n, (function.uncurry (cv n) : (T n × U n) → comp (V n)))) :
--   polynomial_complexity (λ n, (λ t, comp.bind (cu n t) (cv n t))) :=
-- sorry


end complexity_class