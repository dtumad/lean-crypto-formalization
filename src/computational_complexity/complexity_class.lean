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

section poly_time_fun

/-- `poly_time_fun c` means `c` can be evaluated in polynomial time on any input -/
def poly_time_fun {A B : ℕ → Type u} [function_cost_model.{u} ℚ]
  (c : Π n, A n → B n) : Prop :=
∃ (f : ℕ → ℚ), poly_growth f ∧ ∀ n, cost_at_most (c n) (f n)

variables  {A B C D : ℕ → Type u} [function_cost_model.{u} ℚ]

section poly_growth_const

lemma poly_time_fun_of_has_cost_const {A B : ℕ → Type u} {c : Π n, A n → B n} (x : ℚ)
  (hn : ∀ n, cost_at_most (c n) x) : poly_time_fun c :=
⟨λ n, x, poly_growth_const x, hn⟩

@[simp]
lemma poly_time_fun_const (A : ℕ → Type u) {B : ℕ → Type u} (b : Π (n : ℕ), B n) :
  poly_time_fun (λ n, (λ _, b n : A n → B n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, sorry)

@[simp]
lemma poly_time_fun_unit [function_cost_model.{0} ℚ] {A : ℕ → Type} (f : Π n, unit → A n) :
  poly_time_fun f :=
poly_time_fun_of_has_cost_const 0 (λ n, by sorry)

@[simp]
lemma poly_time_fun_fst (A B : ℕ → Type u) :
  poly_time_fun (λ n, (prod.fst : A n × B n → A n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, sorry)

@[simp]
lemma poly_time_fun_snd (A B : ℕ → Type u) :
  poly_time_fun (λ n, (prod.snd : A n × B n → B n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, sorry)

end poly_growth_const

lemma poly_time_fun_comp {c : Π n, A n → B n} {d : Π n, B n → C n}
  (hc : poly_time_fun c) (hd : poly_time_fun d) :
  poly_time_fun (λ n, d n ∘ c n) :=
let ⟨p, hp, hpc⟩ := hc in let ⟨q, hq, hqd⟩ := hd in
⟨p + q, poly_growth_add hp hq, λ n, sorry⟩

lemma poly_time_fun_comp_ext {c : Π n, A n → B n} {d : Π n, B n → C n} {e : Π n, A n → C n}
  (hc : poly_time_fun c) (hd : poly_time_fun d) (he : ∀ n a, e n a = d n (c n a)) :
  poly_time_fun e :=
(funext $ λ n, funext $ λ a, (he n a).symm : (λ n, d n ∘ c n) = e)
  ▸ poly_time_fun_comp hc hd

@[simp]
lemma poly_time_fun_pair_iff [∀ n, inhabited $ A n] [∀ n, inhabited $ C n]
  (c : Π n, A n → B n) (d : Π n, C n → D n) :
  poly_time_fun (λ n, (λ x, (c n x.1, d n x.2) : A n × C n → B n × D n)) ↔
    poly_time_fun c ∧ poly_time_fun d :=
begin
  sorry
  -- refine ⟨_, _⟩,
  -- { rintro ⟨p, hp, h⟩,
  --   exact ⟨⟨p, hp, λ n, has_cost.has_cost_of_prod $ h n⟩,
  --     ⟨p, hp, λ n, has_cost.has_cost_of_prod' $ h n⟩⟩ },
  -- { rintro ⟨⟨p, hp, h⟩, ⟨q, hq, h'⟩⟩,
  --   refine ⟨p + q, poly_growth_add hp hq, λ n, _⟩,
  --   simpa using has_cost.has_cost_prod (h n) (h' n) }
end

end poly_time_fun

section poly_time_comp

variables [function_cost_model.{0} ℚ] [function_cost_model.{1} ℚ]
variable [comp_eval_model ℚ]

def poly_time_comp₀ {T : ℕ → Type} (c : Π n, comp (T n)) : Prop :=
∃ (p : ℕ → ℚ), poly_growth p ∧ ∀ n, cost_at_most (c n) (p n)

/-- `poly_time_comp₁ c` means evaluating `c : A n → comp (T n)` at any `a : A n`,
  and then sampling from the result has polynomial time cost in `n`.
  todo: Essentially non-uniform probabalistic polynomial time -/
def poly_time_comp₁ {A : ℕ → Type} {T : ℕ → Type} (c : Π n, A n → comp (T n)) : Prop :=
∃ (p : ℕ → ℚ), poly_growth p ∧ ∀ n, (cost_at_most (c n) (p n) ∧ ∀ a, cost_at_most (c n a) (p n))

-- -- Can assume that `p` is a positive polynomial. Maybe this should be *baked in* somewhow?
-- lemma iff_pos {A : ℕ → Type*} {T : ℕ → Type} (c : Π n, A n → comp (T n)) :
--   poly_time_comp₁ c ↔ 
--     ∃ p, poly_growth p ∧ ∀ n, 0 ≤ p n ∧ (has_cost (c n) (p n)) ∧ ∀ a, comp_cost (c n a) (p n) :=
-- begin
--   split,
--   {
--     rintro ⟨p, hp, h⟩,
--     refine ⟨p, hp, λ n, _⟩,
--     refine ⟨_, h n⟩,
--     refine has_cost.ge_zero_of_has_cost (h n).1,
--   },
--   {
--     rintro ⟨p, hp, h⟩,
--     refine ⟨p, hp, λ n, (h n).2⟩,
--   }
-- end

-- -- Suffices to seperately prove polynomial complexity in the function and the comp
-- lemma poly_time_comp₁_iff {A : ℕ → Type*} {T : ℕ → Type}
--   (c : Π n, A n → comp (T n)) :
--   poly_time_comp₁ c ↔ poly_time_fun c ∧
--     ∃ p, poly_growth p ∧ ∀ n a, comp_cost (c n a) (p n) :=
-- begin
--   split,
--   {
--     rintro ⟨p, hp, h⟩,
--     refine ⟨⟨p, hp, _⟩, ⟨p, hp, _⟩⟩,
--     refine λ n, (h n).1,
--     refine λ n a, (h n).2 a,
--   },
--   {
--     rintro ⟨⟨p, hp, h⟩, ⟨q, hq, h'⟩⟩,
--     use p + q,
--     split,
--     {
--       exact poly_growth_add hp hq,
--     },
--     refine λ n, ⟨_, _⟩,
--     {
--       refine has_cost.has_cost_of_le _ (h n),
--       simp, sorry,
--       -- refine nonempty.elim (hA n) (λ a, _),
--       -- refine ge_zero_of_comp_cost (h' n a),
--     },
--     {
--       intro a,
--       refine comp_cost.cost_le _ (h' n a),
--       simp,
--       refine has_cost.ge_zero_of_has_cost (h n),
--     }
--   }
-- end

-- variables {T U V : ℕ → Type} {A : ℕ → Type}

-- -- @[simp]
-- -- lemma poly_time_comp₀_ret (t : Π (n : ℕ), T n) :
-- --   poly_time_comp₀ (λ n, comp.ret $ t n) :=
-- -- ⟨0, poly_growth_zero, λ n, comp_cost.cost_ret⟩

-- lemma poly_time_comp₁_ret_iff {A : ℕ → Type*} {T : ℕ → Type}
--   (f : Π n, A n → T n) :
--   poly_time_comp₁ (λ n, (λ t, comp.ret $ f n t)) ↔
--     poly_time_fun f :=
-- begin
--   split,
--   {
--     rintro ⟨p, hp, h⟩,
--     refine ⟨p, hp, λ n, _⟩,
--     specialize h n,
--     simp only [ge_iff_le, comp_cost_ret, has_cost.has_cost_ret_comp_iff] at h,
--     refine h.1,
--   },
--   {
--     rintro ⟨p, hp, h⟩,
--     refine ⟨p, hp, λ n, _⟩,
--     simp,
--     refine ⟨h n, λ _, _⟩,
--     refine has_cost.ge_zero_of_has_cost (h n),
--   }
-- end

-- lemma want_for_bind {A : ℕ → Type*} {T U : ℕ → Type}
--   (f : Π n, A n → (T n))
--   (cb : Π n, A n → (T n → comp (U n)))
--   (hf : poly_time_fun f)
--   (hcb : poly_time_comp₁ (λ n, (λ a, cb n a (f n a)))) :
--   poly_time_comp₁ (λ n, (λ a, comp.bind (comp.ret (f n a)) (cb n a))) :=
-- begin
--   obtain ⟨p, hp, h⟩ := hf,
--   obtain ⟨q, hq, h'⟩ := hcb,
--   refine ⟨p + q + q, poly_growth_add (poly_growth_add hp hq) hq, λ n, _⟩,
--   specialize h n,
--   specialize h' n,
--   simp at h',
--   split,
--   {
--     simp,
--     sorry,
--   },
--   {
--     intro a,
--     apply cost_of_bind_ret,
--     refine comp_cost.cost_le _ (h'.2 _),
--     simp,
--     refine add_nonneg (has_cost.ge_zero_of_has_cost h)
--       (has_cost.ge_zero_of_has_cost h'.1), 
--   }
-- end


end poly_time_comp

end complexity_class