import computational_complexity.cost_model
import computational_complexity.cost_extensions
import analysis.asymptotics.superpolynomial_decay
import computability.tm_computable

universes u v w

/-!
# Computational Complexity Classes

This file defines polynomial and polylogarithmic cost complexity.
The definitions are made in terms of a `cost_model` on the underlying type.

TODO: This really doesn't need to just apply to `ℚ`
-/

/-- Random extra definition aliasing the new mathlib ported version -/
def negligable {R : Type*} [topological_space R] [comm_semiring R] (f : ℕ → R) := 
asymptotics.superpolynomial_decay filter.at_top coe f

open turing computability

def poly_time {α β : Type} (f : α → β) :=
Σ (ea : fin_encoding α) (eb : fin_encoding β),
  tm2_computable_in_poly_time ea eb f

inductive prob_poly_time :
  Π {α β : Type} (f : α → prob_comp β), Type 1

inductive oracle_poly_time {spec : oracle_comp_spec} :
  Π {α β : Type} (f : α → oracle_comp spec β), Type 1

-- /-- Class for pairs of types `α` and `β` such that `α → β` has a notion of polynomial complexity -/
-- class has_poly_time (α : Type u) (β : Type v) :=
-- (poly_time_implementation : (α → β) → Type (max u v + 1))

-- /-- A function is `poly_time` if there is some polynomial time implementation -/
-- def poly_time {α : Type u} {β : Type v} [has_poly_time α β] (f : α → β) :=
-- has_poly_time.poly_time_implementation f

-- /-- Base types have a definition of polynomial time in terms of Turing machines -/
-- instance has_poly_time_base (α β : Type) : has_poly_time α β :=
-- { poly_time_implementation := λ f, Σ (ea : fin_encoding α) (eb : fin_encoding β),
--     tm2_computable_in_poly_time ea eb f }

-- section has_poly_time_base

-- end has_poly_time_base

-- /-- Extend the definition of polynomial time to a monad -/
-- class monadic_poly_time_model (M : Type → Type 1) [monad M] :=
-- (has_poly_time' (α β : Type) : has_poly_time α (M β))
-- (poly_time_return {α β : Type} (f : α → β) (hf : poly_time f) : 
--   poly_time (return ∘ f : α → M β))
-- (poly_time_bind {α β γ : Type} (f : α → M β) (g : α → β → M γ)
--   (hf : poly_time f) (hg : poly_time (function.uncurry g)) :
--   poly_time (λ a, (f a) >>= (g a)))
-- (poly_time_dcomp {α β γ : Type} (f : α → β) (g : α → β → M γ)
--   (hf : poly_time f) (hg : poly_time $ function.uncurry g) :
--   poly_time (g ∘' f))

-- instance monadic_cost_model.has_poly_time (M : Type → Type 1)
--   [monad M] [monadic_poly_time_model M] (α β : Type) : has_poly_time α (M β) :=
-- monadic_poly_time_model.has_poly_time' α β

-- namespace monadic_cost_model


-- end monadic_cost_model

-- class prob_poly_time_model
--   extends monadic_poly_time_model prob_comp

-- namespace prob_poly_time_model


-- end prob_poly_time_model

-- /-- Note : model should assume oracle query has cost `0`,
--   simulation can account for it's own additional cost in lemmas -/
-- class oracle_poly_time_model (spec : oracle_comp_spec) [prob_poly_time_model]
--   extends monadic_poly_time_model (oracle_comp spec) :=
-- (poly_time_sample {α β : Type} (f : α → prob_comp β)
--   (hf : poly_time f) : poly_time (oracle_comp.sample ∘ f : α → oracle_comp spec β))

-- namespace oracle_poly_time_model


-- end oracle_poly_time_model

namespace complexity_class 

open cost_model

def polynomial_complexity {τ : ℕ → Type u} [∀ n, cost_model ℚ (τ n)]
  (c : Π n, τ n) : Prop :=
∃ (f : ℕ → ℚ), poly_growth f ∧ ∀ n, cost_at_most (c n) (f n)

variables {τ : ℕ → Type u} [∀ n, cost_model ℚ (τ n)]

lemma polynomial_complexity_of_cost_le
  (c c' : Π n, τ n) (h : ∀ (n : ℕ) (x : ℚ), cost_at_most (c n) x → cost_at_most (c' n) x)
  (hc : polynomial_complexity c) : polynomial_complexity c' :=
let ⟨p, hp, hpc⟩ := hc in 
  ⟨p, hp, λ n, h n _ $ hpc n⟩

lemma polynomial_complexity_of_has_cost_const 
  (c : Π n, τ n) (x : ℚ) (hn : ∀ n, cost_at_most (c n) x) :
  polynomial_complexity c :=
⟨λ n, x, by simp [poly_growth], hn⟩

@[simp]
lemma polynomial_complexity_of_has_cost_zero 
  (c : Π n, τ n) [hc : ∀ n, cost_zero ℚ (c n)] :
  polynomial_complexity c :=
polynomial_complexity_of_has_cost_const c 0 hc

section compatible_cost_models

variables {A B C D : ℕ → Type*}

variables [∀ n, cost_model ℚ (A n → B n)]
  [∀ n, cost_model ℚ (B n → C n)] [∀ n, cost_model ℚ (A n → C n)]
  [∀ n, compatible_cost_models ℚ (A n) (B n) (C n)]

lemma polynomial_complexity_comp 
  {c : Π n, A n → B n} {d : Π n, B n → C n}
  (hc : polynomial_complexity c) (hd : polynomial_complexity d) :
  polynomial_complexity (λ n, d n ∘ c n : Π n, A n → C n) :=
let ⟨p, hp, hpc⟩ := hc in let ⟨q, hq, hqd⟩ := hd in
⟨p + q, sorry, λ n, 
  compatible_cost_models.cost_at_most_compose (hpc n) (hqd n)⟩

lemma polynomial_complexity_comp_ext 
  {c : Π n, A n → B n} {d : Π n, B n → C n} {e : Π n, A n → C n}
  (hc : polynomial_complexity c) (hd : polynomial_complexity d) 
  (he : ∀ n a, e n a = d n (c n a)) : polynomial_complexity e :=
(funext $ λ n, funext $ λ a, (he n a).symm : (λ n, d n ∘ c n) = e)
  ▸ polynomial_complexity_comp hc hd

end compatible_cost_models

section function_cost_model

variables {A B C D : ℕ → Type}

variables [function_cost_model ℚ]

@[simp]
lemma polynomial_complexity_const [function_cost_model ℚ] (A : ℕ → Type) (b : Π (n : ℕ), B n) :
  polynomial_complexity (λ n, (λ _, b n : A n → B n)) :=
polynomial_complexity_of_has_cost_zero _

section pairing_cost_extension

variables [pairing_cost_extension ℚ]

@[simp]
lemma polynomial_complexity_fst (A B : ℕ → Type) :
  polynomial_complexity (λ n, (prod.fst : A n × B n → A n)) :=
polynomial_complexity_of_has_cost_zero _

@[simp]
lemma polynomial_complexity_snd (A B : ℕ → Type) :
  polynomial_complexity (λ n, (prod.snd : A n × B n → B n)) :=
polynomial_complexity_of_has_cost_zero _

lemma polynomial_complexity_prod_map {A B C D : ℕ → Type}
  {f : Π n, A n → C n} {g : Π n, B n → D n}
  (hf : polynomial_complexity f) (hg : polynomial_complexity g) :
  polynomial_complexity (λ n, (prod.map (f n) (g n) : A n × B n → C n × D n)) :=
let ⟨p, hp, hpf⟩ := hf in let ⟨q, hq, hqg⟩ := hg in
⟨p + q, sorry, λ n, pairing_cost_extension.cost_at_most_prod_map (hpf n) (hqg n)⟩

@[simp]
lemma polynomial_complexity_pair_iff [∀ n, inhabited $ A n] [∀ n, inhabited $ C n]
  (c : Π n, A n → B n) (d : Π n, C n → D n) :
  polynomial_complexity (λ n, (prod.map (c n) (d n) : A n × C n → B n × D n)) ↔
    polynomial_complexity c ∧ polynomial_complexity d :=
begin
  refine ⟨_, _⟩,
  { rintro ⟨p, hp, h⟩,
    refine ⟨⟨p, hp, λ n, _⟩, ⟨p, hp, λ n, _⟩⟩,
    { exact compatible_cost_models.cost_at_most_of_cost_zero_wrap_ext
        (λ a, (a, arbitrary (C n))) _ prod.fst (h n) (by simp) },
    { exact compatible_cost_models.cost_at_most_of_cost_zero_wrap_ext
        (λ c, (arbitrary (A n), c)) _ prod.snd (h n) (by simp) } },
  { rintro ⟨⟨p, hp, h⟩, ⟨q, hq, h'⟩⟩,
    refine ⟨p + q, sorry, λ n, _⟩,
    refine pairing_cost_extension.cost_at_most_prod_map
      (h n) (h' n) }
end

lemma polynomial_complexity_unit_prod (c : Π n, unit × A n → B n)
  (hc : polynomial_complexity (λ n, (λ a, c n ((), a)))) :
  polynomial_complexity c :=
polynomial_complexity_comp_ext
  (polynomial_complexity_snd _ _) hc 
  (λ n a, congr_arg (c n) (prod.ext (unit.ext) rfl))

end pairing_cost_extension

section monadic_cost_model

variables
  (M : Type → Type u) [monad M]
  [monadic_cost_model ℚ M]

lemma polynomial_complexity_pure {A B : ℕ → Type} 
  {f : Π n, A n → B n} (hf : polynomial_complexity f) :
  polynomial_complexity (λ n, (pure ∘ (f n) : A n → M (B n))) :=
let ⟨p, hp, h⟩ := hf in
⟨p, hp, λ n, monadic_cost_model.cost_at_most_pure M (h n)⟩

lemma polynomial_complexity_bind {T U V : ℕ → Type}
  {mu : Π n, T n → M (U n)} {mv : Π n, T n → U n → M (V n)}
  (hmu : polynomial_complexity mu)
  (hmv : polynomial_complexity (λ (n : ℕ), @function.uncurry (T n) (U n) _ (mv n))) :
  polynomial_complexity (λ n, (λ t, bind (mu n t) (mv n t))) :=
let ⟨p, hp, hpmu⟩ := hmu in
let ⟨q, hq, hqmv⟩ := hmv in
⟨p + q, sorry, λ n, monadic_cost_model.cost_at_most_bind (hpmu n) (hqmv n)⟩

section pairing_cost_extension

variable [pairing_cost_extension ℚ]

lemma polynomial_complexity_bind_of_subsingleton {T U V : ℕ → Type}
  [∀ n, subsingleton $ T n] [∀ n, inhabited $ T n]
  {mu : Π n, T n → M (U n)} {mv : Π n, T n → U n → M (V n)}
  (hmu : polynomial_complexity mu)
  (hmv : polynomial_complexity (λ n, mv n $ arbitrary (T n))) :
  polynomial_complexity (λ n, (λ t, bind (mu n t) (mv n t))) :=
begin
  refine polynomial_complexity_bind M hmu 
    (polynomial_complexity_comp_ext (polynomial_complexity_snd T U) hmv _),
  rintros n ⟨t, u⟩,
  simp [subsingleton.elim t (arbitrary $ T n)],
end

end pairing_cost_extension

end monadic_cost_model

section comp_cost_model

variables [function_cost_model ℚ] [comp_cost_model ℚ]

lemma polynomial_complexity_comp_ext'
  {T U : ℕ → Type} {cu cu' : Π n, T n → prob_comp (U n)}
  (h : ∀ (n : ℕ) (t : T n), (cu n t).eval_distribution = (cu' n t).eval_distribution)
  (hcu : polynomial_complexity cu) : polynomial_complexity cu' :=
polynomial_complexity_of_cost_le cu cu'
  (λ n x hx, comp_cost_model.cost_at_most_comp_ext (h n) hx) hcu

lemma polynomial_complexity_ret {T : ℕ → Type} :
  polynomial_complexity (λ n, (return : T n → prob_comp (T n))) :=
polynomial_complexity_of_has_cost_zero _

lemma polynomial_complexity_comp_ret_of_polynomial_complexity
  {T U : ℕ → Type} {c : Π n, T n → U n}
  (hc : polynomial_complexity c) :
  polynomial_complexity (λ n, (λ t, return (c n t) : T n → prob_comp (U n))) :=
polynomial_complexity_comp hc polynomial_complexity_ret

lemma polynomial_complexity_comp_bind
  {T U V : ℕ → Type} {cu : Π n, T n → prob_comp (U n)}
  {cv : Π n, T n → U n → prob_comp (V n)}
  (hcu : polynomial_complexity cu)
  (hcv : polynomial_complexity (λ n, (function.uncurry (cv n) : T n × U n → prob_comp (V n)))) :
  polynomial_complexity (λ n, (λ t, (cu n t) >>= (cv n t) : T n → prob_comp (V n))) :=
begin
  obtain ⟨p, hp, hpcu⟩ := hcu,
  obtain ⟨q, hq, hqcv⟩ := hcv,
  refine ⟨p + q, sorry, λ n, _⟩,
  refine comp_cost_model.cost_at_most_comp_bind (hpcu n) (hqcv n),
end

section product_cost_model

variable [pairing_cost_extension ℚ]

-- TODO: Maybe some namespacing based on cost models would clear up this naming
lemma polynomial_complexity_comp_unit_prod
  [pairing_cost_extension ℚ] [comp_cost_model ℚ]
  {T U : ℕ → Type} (cu : Π n, unit × T n → prob_comp (U n))
  (hcu : polynomial_complexity (λ n, (λ t, cu n ((), t)))) :
  polynomial_complexity cu :=
polynomial_complexity_comp_ext
  (polynomial_complexity_snd _ _) hcu 
  (λ n a, congr_arg (cu n) (prod.ext (unit.ext) rfl))

end product_cost_model

end comp_cost_model

end function_cost_model

end complexity_class