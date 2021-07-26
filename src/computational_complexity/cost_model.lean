import crypto_foundations.comp
import crypto_foundations.oracle_comp
import computational_complexity.polynomial_asymptotics
import to_mathlib

import data.real.nnreal

/-!
# Cost Model for shallow embedding

This file defines a cost model for lean functions, and for instances of `comp`.
Costs are specified by an axiomatically defined proposition `has_cost f n`.
Particular proofs may need to assume additional hypotheses about `has_cost`,
  but properties of most basic functions are defined are defined here.

Since function equiality in Lean is extensional, 
  `has_cost f n → has_cost g n` whenever `f` and `g` are pointwise equal (see `has_cost_ext`).
Therefore `has_cost f n` should be thought of as saying that *some* procedure
  implementing the abstract function `f` has cost `n`,
  rather than as saying that computing `f` directly has cost `n`.

`has_cost` also only defines a lower bound on the cost (see `has_cost_of_le`),
  which is sufficient for establishing reduction in cryptographic proofs.
In particular, it suffices for establishing asymptotic behavior is polynomial / polylogarithmic.

Also note that `has_cost` assumes the input and output of functions has some *fixed* internal representation,
  and all cost statements are being made relative to this fixed representation.
This allows `has_cost` to behave well with function composition,
  but also means all axioms need to be valid in the context of shared representations.
-/

universes u v w

class has_cost_pred (C : Type) (T : Type u)  :=
(cost_pred : T → C → Prop)

def cost_at_most {T : Type u} {C : Type} [has_cost_pred C T] :
  T → C → Prop :=
has_cost_pred.cost_pred

section cost_model

-- TODO: Try to get this working with some extensible system using something like this
/-- Cost model on a type `T` where cost takes values in `C`. -/
class cost_model (C : Type) (T : Type v) [linear_ordered_semiring C]
  extends has_cost_pred C T :=
-- (cost_pred : T → C → Prop)
(cost_trans {x y : C} {t : T} : cost_at_most t x → x ≤ y → cost_at_most t y)
(nonneg_of_has_cost {x : C} {t : T} : cost_at_most t x → 0 ≤ x)

def cost_zero (C : Type) {T : Type v} [linear_ordered_semiring C]
  [cost_model C T] (t : T) : Prop :=
cost_at_most t (0 : C)

end cost_model

section function_cost_model

class function_cost_model (C : Type) [linear_ordered_semiring C] :=
(cm (T U : Type v) : cost_model C (T → U))
(cost_id {T : Type v} : cost_zero C (id : T → T))

instance function_cost_model.cost_model (C : Type)
  [linear_ordered_semiring C] [function_cost_model.{v} C] 
  (T U : Type v) : cost_model C (T → U) :=
function_cost_model.cm T U

end function_cost_model

section monadic_cost_model

class monadic_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{u} C]
  (M : Type → Type u) [monad M] :=
(cm (T U : Type) : cost_model C (T → M U))
(cost_compose {T U V : Type} {x y : C} (f : T → U) (g : U → M V) :
  cost_at_most f x →
  cost_at_most g y →
  cost_at_most (g ∘ f) (x + y))
(cost_compose' {T U V : Type} {x y : C} (f : T → M U) (g : M U → M V) :
  cost_at_most f x →
  cost_at_most g y →
  cost_at_most (g ∘ f) (x + y))
(cost_pure (T : Type) : 
  cost_zero C (pure : T → M T))
(cost_uncurry_bind (T U : Type) :
  cost_zero C (function.uncurry bind : M T × (T → M U) → M U))

instance monadic_cost_model.cost_model (C : Type)
  [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{u} C]
  (M : Type → Type u) [monad M]
  [monadic_cost_model C M] (T U : Type) : cost_model C (T → M U) :=
monadic_cost_model.cm T U 

class monad_eval_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{u} C]
  (M : Type → Type u) [monad M]
  extends monadic_cost_model C M :=
(eval_model (T : Type) : cost_model C (M T))
(cost_eval_pure {T : Type} (t : T) :
  cost_zero C (pure t : M T))
(cost_eval_bind {T U : Type} {x y z : C} (ct : M T) (cu : T → M U) :
  cost_at_most ct x →
  cost_at_most cu y →
  ∀ t, cost_at_most (cu t) z →
  cost_at_most (bind ct cu : M U) (x + y + z))

instance monad_eval_model.cost_model (C : Type)
  [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{u} C]
  (M : Type → Type u) [monad M]
  [monad_eval_model C M] (T : Type) : cost_model C (M T) :=
monad_eval_model.eval_model T


end monadic_cost_model

section comp_cost_model

class comp_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{1} C]
  extends monadic_cost_model C comp :=
(cost_repeat {T : Type} (p : T → Prop) [decidable_pred p] :
  cost_zero C (comp.repeat p))

class comp_eval_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{1} C]
  extends monad_eval_model C comp :=
(cost_rnd_bit : cost_at_most (comp.rnd bool) (1 : C))


end comp_cost_model

section oracle_comp_cost_model

class oracle_comp_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{1} C]
  (T U : Type)
  extends monadic_cost_model C (oracle_comp T U) :=
(cost_oc_query : 
  cost_zero C (oracle_comp.oc_query : T → oracle_comp T U U))

class oracle_comp_eval_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{1} C]
  (T U : Type)
  extends monad_eval_model C (oracle_comp T U) :=
(cost_oc_query (t : T) : cost_zero C (oracle_comp.oc_query t : oracle_comp T U U))


end oracle_comp_cost_model

-- structure wrapper_cost_model (C : Type u) (M : Type → Type v)
--   [linear_ordered_semiring C] :=
-- (cm (T U : Type) : cost_model C (M T → M U))
-- (cost_id {T : Type} : (cm T T).cost_pred id 0)
-- (cost_const {T U : Type} (u : M U) : (cm T U).cost_pred (λ _, u) 0)
-- (cost_compose {T U V : Type} {n m : C}
--   {f : M T → M U} {g : M U → M V} :
--   (cm T U).cost_pred f n →
--   (cm U V).cost_pred g m →
--   (cm T V).cost_pred (g ∘ f) (n + m))

-- section function_cost_model

-- class function_cost_model (C : Type u) [linear_ordered_semiring C]
--   extends wrapper_cost_model C id :=
-- (cost_fst {T U : Type} : (cm (T × U) T).cost_pred prod.fst 0)
-- (cost_snd {T U : Type} : (cm (T × U) U).cost_pred prod.snd 0)

-- instance function.has_cost_pred {A B : Type} (C : Type u)
--   [linear_ordered_semiring C] [fcm : function_cost_model C] :
--   has_cost_pred (A → B) C :=
-- ⟨ cost_model.cost_pred $ fcm.cm A B ⟩

-- end function_cost_model

-- section monadic_cost_model



-- end monadic_cost_model

-- namespace cost_model

-- /-- Need to declare this as a global constant to allow universe level crossing -/
-- constant fcm : ∀ (A : Type u) (B : Type v), cost_model ℚ (A → B)

-- /-- Create a cost model on arbitrary functions (across arbitrary universes). -/
-- noncomputable instance function.cost_model {A B : Type*} :
--   cost_model ℚ (A → B) :=
-- fcm A B

-- constant ccm : ∀ (A : Type), cost_model ℚ (comp A)

-- noncomputable instance comp.cost_model {A : Type} :
--   cost_model ℚ (comp A) :=
-- ccm A

-- constant ocm : ∀ (A B C : Type), cost_model ℚ (oracle_comp A B C × ℚ)

-- noncomputable instance oracle_comp.cost_model {A B C : Type*} :
--   cost_model ℚ (oracle_comp A B C × ℚ) :=
-- ocm A B C

-- axiom cost_swap' (A : Type u) (B : Type v) : cost_at_most 
--   (prod.swap : A × B → B × A) (0 : ℚ)

-- section function_cost_model

-- variables {A B C D : Type*}

-- /-- Assumptions about costs of functions built from other functions -/
-- class function_cost_model :=
-- (cost_id (A : Type*) : cost_at_most (id : A → A) (0 : ℚ))
-- (cost_compose {A B C : Type*} {f : A → B} {g : A → B → C} {n m l : ℚ} 
--   (hf : cost_at_most f n) (hg : cost_at_most g m)
--   (hg' : ∀ a, cost_at_most (g a) l) :
--   cost_at_most (λ a, g a (f a)) (n + m + l))
-- (cost_of_uncurry {A B C : Type*} {f : A → B → C} {n : ℚ}
--   (hf : cost_at_most (function.uncurry f) n) :
--   cost_at_most f n ∧ ∀ a, cost_at_most (f a) n)
-- -- `product` structuring operations
-- (cost_prod {A B C : Type*} (f : A → B) (g : A → C)
--   (n m : ℚ) (hf : cost_at_most f n) (hg : cost_at_most g m) :
--   cost_at_most (λ x, (f x, g x) : A → B × C) (n + m))
-- (cost_fst (A B : Type*) : cost_at_most 
--   (prod.fst : A × B → A) (0 : ℚ))
-- (cost_swap (A B : Type*) : cost_at_most 
--   (prod.swap : A × B → B × A) (0 : ℚ))
-- -- `vector` structuring operations
-- (cost_vector_cons (A : Type*) (n : ℕ) : cost_at_most 
--   (function.uncurry vector.cons : A × vector A n → vector A n.succ) (0 : ℚ))
-- -- `comp` structuring functions
-- (cost_comp_ret (A : Type) : cost_at_most 
--   (comp.ret : A → comp A) (0 : ℚ))
-- (cost_comp_bind (A B : Type) : cost_at_most 
--   (function.uncurry comp.bind : comp A × (A → comp B) → comp B) (0 : ℚ))



-- example (A : Type v) [h : function_cost_model] : cost_at_most (id : A → A) (0 : ℚ) :=
-- begin
--   exact @function_cost_model.cost_id h A,
--   -- exact this,
-- end

-- lemma cost_at_most_comp_of_le [function_cost_model] {A B C : Type*}
--   {f : A → B} {g : B → C} {n m x : ℚ}
--   (hf : cost_at_most f n) (hg : cost_at_most g m) (h : n + m ≤ x) :
--   cost_at_most (g ∘ f) x :=
-- begin
--   sorry,
-- end

-- lemma prod_cost_model.cost_snd (A : Type v) (B : Type u) [fcm : function_cost_model] :
--   cost_at_most (prod.snd : A × B → B) (0 : ℚ) :=
-- begin
--   have : (prod.snd : A × B → B) = prod.fst ∘ prod.swap,
--   from funext (λ x, by simp),
--   rw this,
--   have := cost_swap' A B,
--   have := @function_cost_model.cost_swap fcm A B,
--   refine cost_at_most_comp_of_le 
--     (function_cost_model.cost_swap A B) _ _,
--   sorry,
-- end

-- end function_cost_model

-- section comp_cost_model
-- open comp

-- class comp_cost_model :=
-- (cost_ret {A : Type} (a : A) : cost_at_most (ret a) (0 : ℚ))
-- (cost_bind {A B : Type} {ca : comp A} {cb : A → comp B} {n m l : ℚ}
--   (hca : cost_at_most ca n) (hcb : cost_at_most cb m)
--   (hcb' : ∀ a, cost_at_most (cb a) l) :
--   cost_at_most (ca.bind cb) (n + m + l))
-- (cost_bind_ret {A B : Type} {a : A} {cb : A → comp B} {n : ℚ}
--   (hcb : cost_at_most (cb a) n) :
--   cost_at_most ((ret a).bind cb) n)
-- (cost_rnd_bit : cost_at_most (rnd bool) (1 : ℚ))

-- end comp_cost_model

-- section oracle_comp_cost_model

-- open oracle_comp

-- class oracle_comp_cost_model :=
-- (cost_oc_query {A B : Type} (a : A) (n : ℚ) :
--   cost_at_most (@oc_query A B a, n) n)
-- (cost_oc_ret {A B C : Type} {cc : comp C} {n : ℚ} (hcc : cost_at_most cc n) :
--   ∀ (query_cost : ℚ), cost_at_most (@oc_ret A B C cc, query_cost) n)
-- (cost_oc_bind {A B C D : Type} {oc : oracle_comp A B C} {od : C → oracle_comp A B D} {n m l qc : ℚ}
--   (hoc : cost_at_most (oc, qc) n) (hod : cost_at_most od m)
--   (hod' : ∀ c, cost_at_most (od c, qc) l) :
--   cost_at_most (oc.oc_bind od, qc) (n + m + l))

-- end oracle_comp_cost_model

-- class standard_cost_model extends function_cost_model,
--   comp_cost_model, oracle_comp_cost_model

-- end cost_model

-- namespace cost_model

-- variables {C : Type} {T : Type u} [linear_ordered_semiring C]

-- def function_cost_model' := ∀ (A : Type u) (B : Type v), cost_model ℚ (A → B)
-- def comp_cost_model' := ∀ {A : Type}, cost_model ℚ (comp A)
-- def oracle_comp_cost_model' := ∀ {A B C : Type}, cost_model ℚ (oracle_comp A B C × ℚ)

-- class standard_function_cost_model (fcm : function_cost_model') :=
-- (has_cost_compose {A : Type} {B : Type} {C : Type}
--   {f : A → B} {g : A → B → C} {n1 n2 n3 : ℚ} :
--     (fcm A B).cp f n1 → (fcm A (B → C)).cp g n2 → 
--       (∀ a, (fcm B C).cp (g a) n3) 
--       → (fcm A C).cp (λ a, g a (f a)) (n1 + n2 + n3))

-- class constant_function_cost_model (fcm : function_cost_model')
--   extends standard_function_cost_model fcm :=
-- (has_cost_const {A : Type u} {B : Type v} (b : B) : 
--   (fcm A B).cp (λ _, b : A → B) 0)

-- variables (fcm : function_cost_model')

-- @[simp]
-- lemma has_cost_const_iff
--   (fcm : function_cost_model') [hhh : constant_function_cost_model fcm]
--   {A : Type u} {B : Type v} (b : B) (x : ℚ) : 
--   (fcm A B).cp (λ _, b : A → B) x ↔ 0 ≤ x :=
-- begin
--   split,
--   {
--     intro h,
--     refine (fcm A B).nonneg_of_has_cost h,
--   },
--   {
--     intro h,
--     refine (fcm A B).has_cost_trans _ h,
--     refine @constant_function_cost_model.has_cost_const fcm
--       hhh A B b,
--   }
-- end


-- -- lemma has_cost_trans [cost_model C T] {x y : C}
-- --   {t : T} (h : cost_model.cp t x) (hxy : x ≤ y) : cost_model.cp t y :=
-- -- cost_model.has_cost_trans h hxy

-- end cost_model


-- /-- Represents a cost assignment model to Lean functions -/
-- def function_cost_model := ∀ {A : Type u} {B : Type v}, (A → B) → ℚ → Prop
-- def comp_cost_model := ∀ {A : Type}, comp A → ℚ → Prop
-- def oracle_comp_cost_model := ∀ {A B C : Type}, oracle_comp A B C → (ℚ → ℚ) → Prop

-- /-- Defines an extensible axiomatic cost model for Lean functions.
--   This constant exists over arbitrary universes `u` and `v` until use, 
--     in particular we allow `B` to vary over `Type` and `Type 1`. -/
-- constant has_cost : function_cost_model.{u v}

-- namespace has_cost

-- variables {A : Type u} {B : Type v} {C : Type w} {D : Type*}




-- -- Axioms for deriving costs of functions from related functions

-- -- TODO: Is this worth including? Maybe not useful (maybe makes `poly_growth` easier down the line?)
-- axiom ge_zero_of_has_cost {f : A → B} {n : ℚ} (h : has_cost f n) : n ≥ 0

-- /-- `has_cost` is a lower bound, so any higher cost is also a bound -/
-- axiom has_cost_of_le {f : A → B} {n1 n2 : ℚ} (hnm : n1 ≤ n2) :
--   has_cost f n1 → has_cost f n2

-- /-- Context sensitive composition law, allowing both `g` and `f` to depend on the original value -/
-- axiom has_cost_compose {f : A → B} {g : A → B → C} {n1 n2 n3 : ℚ} :
--     has_cost f n1 → has_cost g n2 → (∀ a, has_cost (g a) n3) 
--       → has_cost (λ a, g a (f a)) (n1 + n2 + n3)

-- /-- evaluating an uncurried function is at most as expensive as evaluating the original on both inputs -/
-- axiom has_cost_uncurry {f : A → B → C} {n1 n2 : ℚ} :
--     has_cost f n1 → (∀ a, has_cost (f a) n2) → has_cost (function.uncurry f) (n1 + n2)

-- /-- evaluating the original function is easier than evaluating the uncurried function -/
-- axiom has_cost_of_uncurry {f : A → B → C} {n : ℚ} :
--     has_cost (function.uncurry f) n → has_cost f n

-- /-- evaluating the origianl function is easier than evaluating the uncurried function -/
-- axiom has_cost_of_uncurry' {f : A → B → C} {n : ℚ} (a : A) :
--     has_cost (function.uncurry f) n → has_cost (f a) n

-- /-- componentwise evaluation is as easy as the two original evaluations -/
-- axiom has_cost_prod {f : A → B} {g : C → D} {n m : ℚ} :
--     has_cost f n → has_cost g m → has_cost (λ (x : A × C), (f x.fst, g x.snd)) (n + m)

-- -- Costs of basic commonly used functions

-- axiom has_cost_const (b : B) :
--   has_cost (λ _, b : A → B) 0

-- axiom has_cost_id (A : Type u) : 
--   has_cost (id : A → A) 0

-- axiom has_cost_fst (A : Type u) (B : Type v) :
--     has_cost (prod.fst : A × B → A) 0

-- axiom has_cost_snd (A : Type u) (B : Type v) :
--     has_cost (prod.snd : A × B → B) 0

-- axiom has_cost_ret (A : Type) :
--   has_cost (comp.ret : A → comp A) 0

-- -- TODO: maybe this shouldn't be an `iff` statement?
-- @[simp]
-- axiom has_cost_ret_comp_iff {A : Type u} {B : Type}
--   (u : A → B) (n : ℚ) : 
--     has_cost (λ a, comp.ret $ u a) n ↔
--       has_cost u n


-- axiom has_cost_bool_eq :
--   has_cost (λ x, x.1 = x.2 : bool × bool → Prop) 0

-- axiom has_cost_prod_fst (A : Type u) (B : Type v) :
--   has_cost (λ a, (λ b, (a, b)) : A → (B → A × B)) 0

-- axiom has_cost_prod_snd {A : Type u} (a : A) (B : Type v) :
--   has_cost (λ b, (a, b) : B → A × B) 0

-- axiom has_cost_prod_swap (A : Type u) (B : Type v) :
--   has_cost (λ x, (x.snd, x.fst) : A × B → B × A) 0

-- axiom has_cost_cons (A : Type) (n : ℕ) :
--   has_cost (λ x, x.1 ::ᵥ x.2 : A × vector A n → vector A (n + 1)) 1

-- -- TODO: Is this the best way to make this?
-- axiom has_cost_unit (A : Type u) : 
--   has_cost (λ a, (a, unit.star) : A → A × unit) 0

-- -- Additional properties derived from the basic axioms

-- -- `has_cost` is extensional, so it only depends on the pointwise function behaviour
-- lemma has_cost_ext {f g : A → B} {n : ℚ} (hf : has_cost f n)
--   (hfg : ∀ a, f a = g a) : has_cost g n :=
-- (funext hfg : f = g) ▸ hf 

-- @[simp] lemma has_cost_id_iff {n : ℚ} : 
--   has_cost (id : A → A) n ↔ n ≥ 0 :=
-- ⟨ge_zero_of_has_cost, λ h, has_cost_of_le h (has_cost_id A)⟩
 
-- @[simp] lemma has_cost_const_iff (A : Type*) (b : B) {n : ℚ} :
--   has_cost (λ _, b : A → B) n ↔ n ≥ 0 :=
-- ⟨ge_zero_of_has_cost, λ h, has_cost_of_le h (has_cost_const _)⟩

-- lemma has_cost_iff_of_const {A B : Type*} (f : A → B)
--   (hf : ∀ a a', f a = f a') (a : A) {n : ℚ} :
--   has_cost f n ↔ n ≥ 0 :=
-- begin
--   convert (has_cost_const_iff A (f a)),
--   exact funext (λ a', hf a' a),
-- end

-- @[simp]
-- lemma has_cost_unit_iff {A : Type*} (f : unit → A)
--   {n : ℚ} : has_cost f n ↔ n ≥ 0 :=
-- has_cost_iff_of_const f (λ a a', congr_arg f unit.ext) ()

-- @[simp] lemma has_cost_fst_iff {n : ℚ} :
--   has_cost (prod.fst : A × B → A) n ↔ n ≥ 0 :=
-- ⟨ge_zero_of_has_cost, λ h, has_cost_of_le h (has_cost_fst A B)⟩

-- @[simp] lemma has_cost_snd_iff {n : ℚ} :
--   has_cost (prod.snd : A × B → B) n ↔ n ≥ 0 :=
-- ⟨ge_zero_of_has_cost, λ h, has_cost_of_le h (has_cost_snd A B)⟩

-- @[simp] lemma has_cost_ret_iff {A : Type} {n : ℚ} :
--   has_cost (comp.ret : A → comp A) n ↔ n ≥ 0 :=
-- ⟨ge_zero_of_has_cost, λ h, has_cost_of_le h (has_cost_ret A)⟩

-- lemma has_cost_comp {f : A → B} {g : B → C} {n m : ℚ} : 
--   has_cost f n → has_cost g m → has_cost (g ∘ f) (n + m) :=
-- λ hf hg, by simpa using has_cost_compose hf (has_cost_const _) (λ _, hg)

-- lemma has_cost_comp_le {f : A → B} {g : B → C} {n m p : ℚ} 
--   (hf : has_cost f n) (hg : has_cost g m) (h : n + m ≤ p) :
--   has_cost (g ∘ f) p :=
-- has_cost_of_le h (has_cost_comp hf hg)

-- lemma has_cost_uncurry_le {f : A → B → C} {n1 n2 n3 : ℚ} (h : n1 + n2 ≤ n3) :
--   has_cost f n1 → (∀ n, has_cost (f n) n2) → has_cost (function.uncurry f) n3 :=
-- λ hf hg, has_cost_of_le h (has_cost_uncurry hf hg)

-- lemma has_cost_curry {A B C : Type} {f : (A × B) → C} {n : ℚ} :
--   has_cost f n → has_cost (function.curry f) n :=
-- λ hf, has_cost_of_uncurry (by simpa using hf)

-- lemma has_cost_prod_snd' {A : Type u} (a : A) (B : Type v) :
--   has_cost (λ b, (b, a) : B → B × A) 0 :=
-- begin
--   refine has_cost_ext 
--     (has_cost_comp_le (has_cost_prod_snd a B)
--       (has_cost_prod_swap A B) $ by ring_nf) _,
--   simp only [implies_true_iff, eq_self_iff_true],
-- end

-- lemma has_cost_prod_le {f : A → B} {g : C → D} {n m p : ℚ}
--   (hf : has_cost f n) (hg : has_cost g m) (h : n + m ≤ p) :
--   has_cost (λ (x : A × C), (f x.fst, g x.snd)) (p) :=
-- has_cost_of_le h (has_cost_prod hf hg)



-- -- TODO: These two proofs could have a tactic sort of thing to solve them.
-- -- Should take in a list of functions, and set the goal as a proof of composition and proof of extensionality
-- lemma has_cost_of_prod {f : A → B} {g : C → D} {n : ℚ} [inhabited C]
--   (h : has_cost (λ (x : A × C), (f x.fst, g x.snd)) n) :
--   has_cost f n :=
-- begin
--   have h1 : has_cost (λ a, (a, arbitrary C) : A → A × C) 0 :=
--     has_cost_prod_snd' (arbitrary C) A,
--   have h2 : has_cost (λ x, x.fst : B × D → B) 0 :=
--     has_cost_fst B D,
--   refine has_cost_ext (has_cost_comp_le h1 (has_cost_comp h h2) $ by linarith) _,
--   simp only [implies_true_iff, eq_self_iff_true],
-- end

-- lemma has_cost_of_prod' {f : A → B} {g : C → D} {n : ℚ} [inhabited A]
--   (h : has_cost (λ (x : A × C), (f x.fst, g x.snd)) n) :
--   has_cost g n :=
-- begin
--   have h1 : has_cost (λ c, (arbitrary A, c) : C → A × C) 0 :=
--     has_cost_prod_snd (arbitrary A) C,
--   have h2 : has_cost (λ x, x.snd : B × D → D) 0 :=
--     has_cost_snd B D,
--   refine has_cost_ext (has_cost_comp_le h1 (has_cost_comp h h2) $ by linarith) _,
--   simp only [implies_true_iff, eq_self_iff_true],
-- end

-- end has_cost










-- -- section comp_cost
-- open comp

-- /-- Cost of a computation `ca : comp A`, relative to a given `function_cost_model`.
--   This represents the cost to query an element of `A` from a `comp A` -/
-- inductive comp_cost : comp_cost_model
-- | cost_ret {A : Type} {a : A} :
--     comp_cost (ret a) 0
-- | cost_bind {A B : Type} {ca : comp A} {cb : A → comp B} {n1 n2 n3 : ℚ} :
--     comp_cost ca n1 → has_cost cb n2 → (∀ a ∈ ca.support, comp_cost (cb a) n3) → comp_cost (ca.bind cb) (n1 + n2 + n3)
-- | cost_rnd_bitvec {n : ℕ} :
--     comp_cost (rnd (bitvec n)) ↑n
-- | cost_le {A : Type} {ca : comp A} {n m : ℚ} (hnm : n ≤ m) :
--     comp_cost ca n → comp_cost ca m

-- axiom cost_of_bind_ret {A B : Type} (a : A) (cb : A → comp B) (n : ℚ)
--   (h : comp_cost (cb a) n) :
--   comp_cost (comp.bind (comp.ret a) cb) n

-- -- This statement holds for `has_cost` as well, but is only provable for `comp_cost`.
-- theorem ge_zero_of_comp_cost {A : Type} {ca : comp A} {n : ℚ} (h : comp_cost ca n) :
--   n ≥ 0 :=
-- begin
--   sorry,
--   -- refine h.rec_on _ _ _ _,
--   -- { refine λ _ _, le_rfl },
--   -- { refine λ A B ca cb n1 n2 n3 _ hcb _ hn1 hn3, _,
--   --   refine add_nonneg (add_nonneg hn1 _) (hn3 (comp_base_exists ca) _),
--   --   refine has_cost.ge_zero_of_has_cost hcb },
--   -- { refine nat.cast_nonneg },
--   -- { refine λ A ca n m hnm hca hn, le_trans hn hnm }
-- end

-- @[simp] lemma comp_cost_ret {A : Type} {a : A} {n : ℚ} :
--   comp_cost (ret a) n ↔ n ≥ 0 :=
-- ⟨ge_zero_of_comp_cost, λ h, comp_cost.cost_le h comp_cost.cost_ret⟩

-- @[simp] lemma comp_cost_rnd_bitvec (n : ℕ) : comp_cost (rnd (bitvec n)) n :=
-- comp_cost.cost_rnd_bitvec

-- lemma comp_cost_rnd_le {n m : ℕ} (hnm : n ≤ m) : comp_cost (rnd (bitvec n)) m :=
-- comp_cost.cost_le (nat.cast_le.mpr hnm) comp_cost.cost_rnd_bitvec

-- lemma comp_cost_bind_of_le {A B : Type} (ca : comp A)
--   (cb : A → comp B) (n1 n2 n3 p : ℚ)
--   (hca : comp_cost ca n1) (hcb : has_cost cb n2)
--   (hcb' : ∀ a ∈ ca.support, comp_cost (cb a) n3) (h : n1 + n2 + n3 ≤ p) :
--   comp_cost (ca >>= cb) p :=
-- comp_cost.cost_le h (comp_cost.cost_bind hca hcb hcb')

-- open oracle_comp

-- -- Returning the result of a `comp` has cost independent of oracle access cost
-- -- Querying the oracle has the same cost as the specified oracle call cost
-- /-- The cost of an `oracle_comp` is a map from the cost of the
--   oracle to the cost of sampling from the `oracle_comp` -/
-- inductive oracle_cost (fm : function_cost_model.{0 1}) (cm : comp_cost_model) : oracle_comp_cost_model
-- | cost_query {A B : Type} {a : A} :
--     oracle_cost (oc_query a : oracle_comp A B B) id
-- | cost_ret {A B C : Type} {c : comp C} {n : ℚ} :
--     cm c n → oracle_cost (oc_ret c : oracle_comp A B C) (λ _, n)
-- | cost_bind {A B C D : Type} {oc : oracle_comp A B C} {od : C → oracle_comp A B D} {n1 n2 n3 : ℕ} :
--     oracle_cost oc n1 → fm od n2 → (∀ c, oracle_cost (od c) n3) 
--       → oracle_cost (oc_bind oc od) (n1 + n2 + n3)
-- | cost_le {A B C : Type} {oc : oracle_comp A B C} {f g : ℚ → ℚ} (hnm : ∀ n, f n ≤ g n) :
--     oracle_cost oc f → oracle_cost oc g

-- -- end comp_cost
