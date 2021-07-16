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

/-- `c ∈ complexity_class C growth_pred cost_pred` means there is some `f` satisfying `growth_pred`
such that `c` and `f` jointly satisfy the cost predicate for all `n`. -/
def complexity_class {ι G : Type*} (C : ι → Type*) 
  (growth_pred : (ι → G) → Prop) (cost_pred : Π (i : ι), C i → G → Prop) :
  set (Π n, C n) :=
{c | ∃ (f : ι → G), growth_pred f ∧ (∀ n, cost_pred n (c n) (f n))}

lemma mem_complexity_class_iff {ι G : Type*} {C : ι → Type*} (c : Π n, C n)
  (growth_pred : (ι → G) → Prop) (cost_pred : Π (i : ι), C i → G → Prop) : 
  c ∈ complexity_class C growth_pred cost_pred ↔
    ∃ (f : ι → G), growth_pred f ∧ (∀ n, cost_pred n (c n) (f n)) :=
iff.rfl

namespace complexity_class 


section poly_time_fun

/-- `poly_time_fun₁ c` means `c` can be evaluated in polynomial time on any input -/
def poly_time_fun₁ {A B : ℕ → Type} (c : Π n, A n → B n) : Prop :=
c ∈ complexity_class (λ n, A n → B n) 
  poly_growth (λ n c x, has_cost c x)
  
variables  {A B C D : ℕ → Type}

section poly_growth_const

lemma poly_time_fun₁_of_has_cost_const {A B : ℕ → Type*} {c : Π n, A n → B n} {x : ℚ}
  (hn : ∀ n, has_cost (c n) x) : poly_time_fun₁ c :=
⟨λ n, x, poly_growth_const x, hn⟩

@[simp]
lemma poly_time_fun₁_const (A : ℕ → Type*) {B : ℕ → Type*} (b : Π (n : ℕ), B n) :
  poly_time_fun₁ (λ n, (λ _, b n : A n → B n)) :=
poly_time_fun₁_of_has_cost_const (λ n, has_cost.has_cost_const (b n))

@[simp]
lemma poly_time_fun₁_fst (A B : ℕ → Type*) :
  poly_time_fun₁ (λ n, (prod.fst : A n × B n → A n)) :=
poly_time_fun₁_of_has_cost_const (λ n, has_cost.has_cost_fst (A n) (B n))

@[simp]
lemma poly_time_fun₁_snd (A B : ℕ → Type*) :
  poly_time_fun₁ (λ n, (prod.snd : A n × B n → B n)) :=
poly_time_fun₁_of_has_cost_const (λ n, has_cost.has_cost_snd (A n) (B n))

end poly_growth_const

lemma poly_time_fun₁_comp {c : Π n, A n → B n} {d : Π n, B n → C n}
  (hc : poly_time_fun₁ c) (hd : poly_time_fun₁ d) :
  poly_time_fun₁ (λ n, d n ∘ c n) :=
let ⟨p, hp, hpc⟩ := hc in let ⟨q, hq, hqd⟩ := hd in
⟨p + q, poly_growth_add hp hq, λ n, has_cost.has_cost_comp (hpc n) (hqd n)⟩

lemma poly_time_fun₁_comp_ext {c : Π n, A n → B n} {d : Π n, B n → C n} {e : Π n, A n → C n}
  (hc : poly_time_fun₁ c) (hd : poly_time_fun₁ d) (he : ∀ n a, e n a = d n (c n a)) :
  poly_time_fun₁ e :=
(funext $ λ n, funext $ λ a, (he n a).symm : (λ n, d n ∘ c n) = e)
  ▸ poly_time_fun₁_comp hc hd

@[simp]
lemma poly_time_fun₁_pair_iff [∀ n, inhabited $ A n] [∀ n, inhabited $ C n]
  (c : Π n, A n → B n) (d : Π n, C n → D n) :
  poly_time_fun₁ (λ n, (λ x, (c n x.1, d n x.2) : A n × C n → B n × D n)) ↔
    poly_time_fun₁ c ∧ poly_time_fun₁ d :=
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

def poly_time_comp₀ {T : ℕ → Type} (c : Π n, comp (T n)) : Prop :=
c ∈ complexity_class (λ n, comp $ T n)
  poly_growth (λ n c x, comp_cost c x)

def poly_time_comp₁ {A T : ℕ → Type} (c : Π n, A n → comp (T n)) : Prop :=
c ∈ complexity_class (λ n, A n → comp (T n)) 
  poly_growth (λ n c x, has_cost c x ∧ ∀ a, comp_cost (c a) x)

lemma test {T : ℕ → Type} (c : Π n, unit → comp (T n)) :
  poly_time_comp₁ c ↔ poly_time_comp₀ (λ n, c n ()) :=
begin
  split,
  {
    rintro ⟨p, hp, hc⟩,
    refine ⟨p, hp, λ n, _⟩,
    specialize hc n,
    replace hc := hc.2,
    refine hc _,
  },
  {
    rintro ⟨p, hp, hc⟩,
    refine ⟨p, hp, λ n, ⟨_, λ a, _⟩⟩,
    {
      simp,
      sorry,
    },
    {
      convert hc n,
    }
  }
end

variables {T U V : ℕ → Type} {A : ℕ → Type}

@[simp]
lemma poly_time_comp₀_ret (t : Π (n : ℕ), T n) :
  poly_time_comp₀ (λ n, comp.ret $ t n) :=
⟨0, poly_growth_zero, λ n, comp_cost.cost_ret⟩

@[simp]
lemma poly_time_comp₁_ret_iff (u : Π (n : ℕ), A n → T n) :
  poly_time_comp₁ (λ n a, comp.ret $ u n a : Π n, A n → comp (T n)) ↔
    poly_time_fun₁ u :=
begin
  split;
  rintro ⟨p, hp, h⟩,
  {
    refine ⟨p, hp, λ n, _⟩,
    specialize h n,
    replace h := h.1,
    simp only [] at h,
    rwa has_cost.has_cost_ret_comp_iff (u n) at h,
  },
  {
    refine ⟨p, hp, λ n, _⟩,
    specialize h n,
    simp [h],
    -- TODO: Can always choose a `p` so this is positive
    sorry,
  }
end

@[simp]
lemma poly_time_comp₀_bind_iff (ct : Π n, comp (T n))
  (cu : Π n, T n → comp (U n)) :
  poly_time_comp₀ (λ n, comp.bind (ct n) (cu n)) ↔
    poly_time_comp₀ ct ∧ poly_time_comp₁ cu :=
begin 
  split,
  {
    rintro ⟨p, hp, h⟩,
    refine ⟨⟨p, hp, λ n, _⟩, ⟨p, hp, λ n, _⟩⟩,
    sorry,
    sorry,
  },
  {
    rintro ⟨⟨p, hp, hp'⟩, ⟨q, hq, hq'⟩⟩,
    refine ⟨p + q + q, _, λ n, _⟩,
    { refine poly_growth_add _ hq,
      exact poly_growth_add hp hq },
    refine comp_cost.cost_bind (hp' n) (hq' n).1 (hq' n).2,
  }
end

@[simp]
lemma poly_time_comp₀_bind_ret_iff (ct : Π n, comp (T n))
  (u : Π n, T n → U n) :
  poly_time_comp₀ (λ n, comp.bind (ct n) (λ t, comp.ret (u n t))) ↔
    (poly_time_comp₀ ct ∧ poly_time_fun₁ u) :=
begin
  simp only [poly_time_comp₀_bind_iff, and.congr_right_iff],
  intro h,
  clear h,
  split,
  {
    rintro ⟨p, hp, hpc⟩,
    refine ⟨p, hp, λ n, _⟩,
    specialize hpc n,
    replace hpc := hpc.1,
    sorry,
  },
  {

    rintro ⟨p, hp, hpc⟩,
    refine ⟨p, hp, λ n, _⟩,
    specialize hpc n,
    -- TODO: need `p` to be positive
    simp,
    sorry,
  }
end

end poly_time_comp

end complexity_class