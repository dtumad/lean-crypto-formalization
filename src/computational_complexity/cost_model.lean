import crypto_foundations.comp
import crypto_foundations.oracle_comp
import computational_complexity.polynomial_asymptotics
import to_mathlib

import data.real.nnreal

/-!
# Cost Model for shallow embedding

TODO: Update all of this documentation.

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

/-- Cost model on a type `T` where cost takes values in `C`. -/
class cost_model (C : Type) (T : Type v) [linear_ordered_semiring C] :=
(cost_pred : T → C → Prop)
(cost_trans {x y : C} {t : T} : cost_pred t x → x ≤ y → cost_pred t y)
(nonneg_of_has_cost {x : C} {t : T} : cost_pred t x → 0 ≤ x)

variables {C : Type} [linear_ordered_semiring C] {T : Type u}

namespace cost_model

def cost_at_most {T : Type u} {C : Type} [linear_ordered_semiring C]
  [cost_model C T] (t : T) (x : C) : Prop :=
cost_model.cost_pred t x

@[class]
def cost_zero (C : Type) {T : Type u} [linear_ordered_semiring C]
  [cost_model C T] (t : T) : Prop :=
cost_at_most t (0 : C)

@[simp]
lemma cost_at_most_iff_nonneg_of_cost_zero [cost_model C T]
  (x : C) (t : T) [ht : cost_zero C t] :
  cost_at_most t x ↔ 0 ≤ x :=
⟨λ htx, cost_model.nonneg_of_has_cost htx, λ hx, cost_model.cost_trans ht hx⟩

lemma cost_at_most_ext [cost_model C T] {t t' : T} {x y : C}
  (htx : cost_at_most t x) (hxy : x ≤ y) (ht : t = t') :
  cost_at_most t' y :=
cost_model.cost_trans (ht ▸ htx : cost_at_most t' x) hxy

lemma cost_zero_ext [cost_model C T] {t t' : T}
  (htx : cost_zero C t) (hxy : t = t') : cost_zero C t' :=
cost_at_most_ext htx le_rfl hxy

end cost_model


open cost_model

class function_cost_model (C : Type) [linear_ordered_semiring C] :=
(cm (T U : Type u) : cost_model C (T → U))
(cost_at_most_compose {T U V : Type u} {x y : C} {f : T → U} {g : U → V} :
  cost_at_most f x → cost_at_most g y → cost_at_most (g ∘ f) (x + y))
(cost_zero_id (T : Type u) : cost_zero C (id : T → T))
(cost_zero_const (T : Type u) {U : Type u} (u : U) : cost_zero C (λ (t : T), u))

instance function_cost_model.cost_model (C : Type)
  [linear_ordered_semiring C] [function_cost_model.{u} C] 
  (T U : Type u) : cost_model C (T → U) :=
function_cost_model.cm T U 

namespace function_cost_model

variables [function_cost_model.{u} C]

instance cost_zero_id' (T : Type u) : 
  cost_zero C (id : T → T) :=
function_cost_model.cost_zero_id T

instance cost_zero_const' (T : Type u) {U : Type u} (u : U) : 
  cost_zero C (λ _, u : T → U) :=
function_cost_model.cost_zero_const T u

instance cost_zero_of_subsingleton_right {T U : Type u} (f : T → U)
  [hT : nonempty T] [subsingleton U] : cost_zero C f :=
begin
  by_cases hU : nonempty U,
  { exact hU.elim (λ u, cost_zero_ext (cost_zero_const T u) $ by simp) },
  { exact absurd (hT.elim (λ t, ⟨f t⟩) : nonempty U) hU }
end

instance cost_zero_of_subsingleton_left {T U : Type u} (f : T → U)
  [hT : nonempty T] [subsingleton T] : cost_zero C f :=
hT.elim (λ t, cost_zero_ext (cost_zero_const T (f t)) (funext (λ t', congr_arg f (by simp))))

lemma cost_at_most_compose_ext {T U V : Type u}
  {f : T → U} {g : U → V} {h : T → V} {x y z : C}
  (hf : cost_at_most f x) (hg : cost_at_most g y)
  (hxyz : x + y ≤ z) (hfg : ∀ t, g (f t) = h t) :
  cost_at_most h z :=
cost_at_most_ext (cost_at_most_compose hf hg) hxyz (funext hfg)

lemma cost_at_most_compose_of_le {T U V : Type u}
  {f : T → U} {g : U → V} {x y z : C}
  (hf : cost_at_most f x) (hg : cost_at_most g y) (hxyz : x + y ≤ z) :
  cost_at_most (g ∘ f) z :=
cost_at_most_compose_ext hf hg hxyz (λ _, rfl)

lemma cost_at_most_compose_of_cost_zero_left [function_cost_model.{u} C]
  {T U V : Type u} (f : T → U) [hf : cost_zero C f]
  {g : U → V} {x : C} (hg : cost_at_most g x) :
  cost_at_most (g ∘ f) x :=
cost_at_most_compose_of_le hf hg (by simp)

lemma cost_at_most_compose_of_cost_zero_right [function_cost_model.{u} C]
  {T U V : Type u} (g : U → V) [hg : cost_zero C g]
  {f : T → U} {x : C} (hf : cost_at_most f x)  :
  cost_at_most (g ∘ f) x :=
cost_at_most_compose_of_le hf hg (by simp)

instance cost_zero_compose [function_cost_model.{u} C]
  {T U V : Type u} (f : T → U) (g : U → V)
  [cost_zero C f] [hg : cost_zero C g] :
  cost_zero C (g ∘ f) :=
cost_at_most_compose_of_cost_zero_left f hg


end function_cost_model


class pairing_cost_model (C : Type) [linear_ordered_semiring C]
  extends function_cost_model.{u} C :=
(cost_zero_fst (T U : Type u) : cost_zero C (prod.fst : T × U → T))
(cost_zero_swap (T U : Type u) : cost_zero C (prod.swap : T × U → U × T))
(cost_at_most_map_fst (T T' U : Type u) {x : C} (f : T → T')
  (hf : cost_at_most f x) : cost_at_most (λ (tu : T × U), (f tu.1, tu.2)) x)
(cost_of_uncurry (T U V : Type u) {x : C} (f : T → U → V)
  (hf : cost_at_most (function.uncurry f) x) :
  cost_at_most f x ∧ ∀ t, cost_at_most (f t) x)

namespace pairing_cost_model

variables [pairing_cost_model.{u} C]

instance cost_zero_fst' (T U : Type u) :
  cost_zero C (@prod.fst T U) :=
cost_zero_fst T U

instance cost_zero_swap' (T U : Type u) : 
  cost_zero C (prod.swap : T × U → U × T) :=
cost_zero_swap T U

instance cost_zero_snd (T U : Type u) : 
  cost_zero C (prod.snd : T × U → U) :=
cost_zero_ext (function_cost_model.cost_zero_compose prod.swap prod.fst) 
  (funext $ by simp)

lemma cost_at_most_map_snd 
  (T U U' : Type u) {x : C} (g : U → U')
  (hg : cost_at_most g x) :
  cost_at_most (λ (tu : T × U), (tu.1, g tu.2)) x :=
begin
  have := pairing_cost_model.cost_at_most_map_fst U U' T g hg,
  have := function_cost_model.cost_at_most_compose (pairing_cost_model.cost_zero_swap T U) this,
  have := function_cost_model.cost_at_most_compose this (pairing_cost_model.cost_zero_swap U' T),
  refine cost_at_most_ext this (by simp) (funext $ by simp),
end

lemma cost_at_most_map_pair
  (T T' U U' : Type u) {x y : C} (f : T → T') (g : U → U')
  (hf : cost_at_most f x) (hg : cost_at_most g y) :
  cost_at_most (λ (tu : T × U), (f tu.1, g tu.2)) (x + y) :=
begin
  have hf' := pairing_cost_model.cost_at_most_map_fst T T' U f hf,
  have hg' := cost_at_most_map_snd T' U U' g hg,
  have := function_cost_model.cost_at_most_compose hf' hg',
  refine cost_at_most_ext this (by simp) (funext $ by simp),
end

end pairing_cost_model


/-- Cost model on `T → M U` represents cost to evaluate at `t` and then
  'evaluate' the resulting monad (e.g. sample from the distribution of a `comp`).
  Monads that add 'non-trivial' functionality e.g. `comp.rnd`,
  will need to specify the evaluation costs of these functionalities -/
class monadic_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{u} C]
  (M : Type → Type u) [monad M] :=
(cm (T U : Type) : cost_model C (T → M U))
(cost_pure (T : Type) : 
  cost_zero C (pure : T → M T))
(cost_bind (T U A : Type) {x y : C} (t : A → M T) (u : A → T → M U)
  (ht : cost_at_most t x)
  (hu : cost_at_most (function.uncurry u) y) :
  cost_at_most (λ a, bind (t a) (u a)) (x + y))
(cost_compatible_left {T U V : Type} {x y : C} 
  (f : T → U) (g : U → M V) :
  cost_at_most f x → cost_at_most g y → cost_at_most (g ∘ f) (x + y))
(cost_compatible_right {T U V : Type} {x y : C} 
  (f : T → M U) (g : M U → M V) :
  cost_at_most f x → cost_at_most g y → cost_at_most (g ∘ f) (x + y))

instance monadic_cost_model.cost_model (C : Type)
  [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{u} C]
  (M : Type → Type u) [monad M]
  [monadic_cost_model C M] (T U : Type) : cost_model C (T → M U) :=
monadic_cost_model.cm T U 

namespace monadic_cost_model

variables [function_cost_model.{0} C] [function_cost_model.{u} C]
  (M : Type → Type u) [monad M] [monadic_cost_model C M]


end monadic_cost_model


class comp_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{1} C]
  extends monadic_cost_model C comp :=
(cost_rnd_bitvec {n : ℕ} : cost_at_most (λ (_ : unit), comp.rnd (vector bool n)) (n : C))

namespace comp_cost_model


end comp_cost_model


class oracle_comp_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model.{0} C] [function_cost_model.{1} C]
  (T U : Type)
  extends monadic_cost_model C (oracle_comp T U) :=
(cost_oc_query : 
  cost_zero C (oracle_comp.oc_query : T → oracle_comp T U U))

namespace oracle_comp_cost_model


end oracle_comp_cost_model

