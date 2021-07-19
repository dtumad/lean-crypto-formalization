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

namespace complexity_class 


section poly_time_fun

/-- `poly_time_fun c` means `c` can be evaluated in polynomial time on any input -/
def poly_time_fun {A B : ℕ → Type*} (c : Π n, A n → B n) : Prop :=
∃ f, poly_growth f ∧ ∀ n, has_cost (c n) (f n)

variables  {A B C D : ℕ → Type}

section poly_growth_const

lemma poly_time_fun_of_has_cost_const {A B : ℕ → Type*} {c : Π n, A n → B n} (x : ℚ)
  (hn : ∀ n, has_cost (c n) x) : poly_time_fun c :=
⟨λ n, x, poly_growth_const x, hn⟩

@[simp]
lemma poly_time_fun_const (A : ℕ → Type*) {B : ℕ → Type*} (b : Π (n : ℕ), B n) :
  poly_time_fun (λ n, (λ _, b n : A n → B n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, has_cost.has_cost_const (b n))

@[simp]
lemma poly_time_fun_unit {A : ℕ → Type*} (f : Π n, unit → A n) :
  poly_time_fun f :=
poly_time_fun_of_has_cost_const 0 (λ n, by simp)

@[simp]
lemma poly_time_fun_fst (A B : ℕ → Type*) :
  poly_time_fun (λ n, (prod.fst : A n × B n → A n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, has_cost.has_cost_fst (A n) (B n))

@[simp]
lemma poly_time_fun_snd (A B : ℕ → Type*) :
  poly_time_fun (λ n, (prod.snd : A n × B n → B n)) :=
poly_time_fun_of_has_cost_const 0 (λ n, has_cost.has_cost_snd (A n) (B n))

end poly_growth_const

lemma poly_time_fun_comp {c : Π n, A n → B n} {d : Π n, B n → C n}
  (hc : poly_time_fun c) (hd : poly_time_fun d) :
  poly_time_fun (λ n, d n ∘ c n) :=
let ⟨p, hp, hpc⟩ := hc in let ⟨q, hq, hqd⟩ := hd in
⟨p + q, poly_growth_add hp hq, λ n, has_cost.has_cost_comp (hpc n) (hqd n)⟩

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
  refine ⟨_, _⟩,
  { rintro ⟨p, hp, h⟩,
    exact ⟨⟨p, hp, λ n, has_cost.has_cost_of_prod $ h n⟩,
      ⟨p, hp, λ n, has_cost.has_cost_of_prod' $ h n⟩⟩ },
  { rintro ⟨⟨p, hp, h⟩, ⟨q, hq, h'⟩⟩,
    refine ⟨p + q, poly_growth_add hp hq, λ n, _⟩,
    simpa using has_cost.has_cost_prod (h n) (h' n) }
end

end poly_time_fun

section poly_time_comp

/--`poly_time_comp₀ c` means sampling from `c : comp (T n)` has polynomial time cost in `n` -/
def poly_time_comp₀ {T : ℕ → Type} (c : Π n, comp (T n)) : Prop :=
∃ p, poly_growth p ∧ ∀ n, comp_cost (c n) (p n)

/-- `poly_time_comp₁ c` means evaluating `c : A n → comp (T n)` at any `a : A n`,
  and then sampling from the result has polynomial time cost in `n`.
  todo: Essentially non-uniform probabalistic polynomial time -/
def poly_time_comp₁ {A T : ℕ → Type} (c : Π n, A n → comp (T n)) : Prop :=
∃ p, poly_growth p ∧ ∀ n, (has_cost (c n) (p n) ∧ ∀ a, comp_cost (c n a) (p n))

-- Suffices to seperately prove polynomial complexity in the function and the comp
lemma poly_time_comp₁_iff {A T : ℕ → Type} [hA : ∀ n, nonempty (A n)]
  (c : Π n, A n → comp (T n)) :
  poly_time_comp₁ c ↔ poly_time_fun c ∧
    ∃ p, poly_growth p ∧ ∀ n a, comp_cost (c n a) (p n) :=
begin
  split,
  {
    rintro ⟨p, hp, h⟩,
    refine ⟨⟨p, hp, _⟩, ⟨p, hp, _⟩⟩,
    refine λ n, (h n).1,
    refine λ n a, (h n).2 a,
  },
  {
    rintro ⟨⟨p, hp, h⟩, ⟨q, hq, h'⟩⟩,
    use p + q,
    split,
    {
      exact poly_growth_add hp hq,
    },
    refine λ n, ⟨_, _⟩,
    {
      refine has_cost.has_cost_of_le _ (h n),
      simp,
      refine nonempty.elim (hA n) (λ a, _),
      refine ge_zero_of_comp_cost (h' n a),
    },
    {
      intro a,
      refine comp_cost.cost_le _ (h' n a),
      simp,
      refine has_cost.ge_zero_of_has_cost (h n),
    }
  }
end

variables {T U V : ℕ → Type} {A : ℕ → Type}

@[simp]
lemma poly_time_comp₀_ret (t : Π (n : ℕ), T n) :
  poly_time_comp₀ (λ n, comp.ret $ t n) :=
⟨0, poly_growth_zero, λ n, comp_cost.cost_ret⟩

end poly_time_comp

end complexity_class