import crypto_foundations.computational_monads.oracle_comp
import computational_complexity.polynomial_asymptotics
import to_mathlib

/-!
# Cost Model for shallow embedding

This file defines an extensible cost model for lean fucntions,
  as well as functions extended with `comp` or `oracle_comp A B` monads.
A model `cost_model C T` define a predicate `cost_at_most (t : T) (c : C)`,
  such that `cost_at_most t x → cost_at_most t y` whenever `x ≤ y`.
`cost_at_most t x` semantically means `t` can be evaluated in time at most `x`,
  although it doesn't say that it can't be evaluated more quickly.
This suffices for proving an algorithm is at least a certain speed,
  and in particular for proving that an algorithm or reduction is polynomial time

Since function equiality in Lean is extensional, 
  `cost_at_most f n → cost_at_most g n` whenever `f` and `g` are pointwise equal.
Therefore `cost_at_most f n` should be thought of as saying that *some* procedure
  implementing the abstract functional behaviour of `f` has cost `n`,
  rather than as saying that computing `f` directly has cost `n`.

Also note that `cost_at_most` assumes the input and output of functions has some *fixed* internal representation,
  and all cost statements are made relative to this fixed representation.

Cost models are defined for the following types:
* `function_cost_model` → `cost_model C (T → U)`
* `comp_cost_model` → `cost_model C (T → comp U)`
* `oracle_comp_cost_model A B` → `cost_model C (T → oracle_comp A B U)`

The cost model on a function `f : T → U` represents the cost of evaluating `f` on an arbitrary input.
For a function of the form `f : T → comp U`, it represents the cost of evaluating `f` on an input,
  and sampling some `U` from the resulting `comp U`.

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

class compatible_cost_models (C : Type) [linear_ordered_semiring C]
  (U : Type u) (V : Type v) (W : Type w)
  [cost_model C (U → V)] [cost_model C (V → W)]
  [cost_model C (U → W)] :=
(cost_at_most_compose {f : U → V} {g : V → W} {x y : C}
  (hf : cost_at_most f x) (hg : cost_at_most g y) :
  cost_at_most (g ∘ f : U → W) (x + y))

namespace compatible_cost_models

variables {U : Type u} {V : Type v} {W : Type w}
  [cost_model C (U → V)] [cost_model C (V → W)] [cost_model C (U → W)]
  [compatible_cost_models C U V W]

lemma cost_at_most_compose_ext
  {f : U → V} {g : V → W} {h : U → W} {x y z : C}
  (hf : cost_at_most f x) (hg : cost_at_most g y)
  (hxyz : x + y ≤ z) (hfg : ∀ t, g (f t) = h t) :
  cost_at_most h z :=
cost_at_most_ext (cost_at_most_compose hf hg) hxyz (funext hfg)

lemma cost_at_most_compose_of_le
  {f : U → V} {g : V → W} {x y z : C}
  (hf : cost_at_most f x) (hg : cost_at_most g y) (hxyz : x + y ≤ z) :
  cost_at_most (g ∘ f) z :=
cost_at_most_compose_ext hf hg hxyz (λ _, rfl)

lemma cost_at_most_of_cost_zero_left_ext
  {x : C} (f : U → V) (g : V → W) {h : U → W}
   [hf : cost_zero C f] (hg : cost_at_most g x) 
   (hgf : ∀ t, g (f t) = h t) : cost_at_most h x :=
cost_at_most_compose_ext hf hg (by simp) hgf

lemma cost_at_most_of_cost_zero_left {x : C} 
  (f : U → V) {g : V → W}
  [cost_zero C f] (hg : cost_at_most g x) : cost_at_most (g ∘ f) x :=
cost_at_most_of_cost_zero_left_ext f g hg (λ t, rfl)

lemma cost_at_most_of_cost_zero_right_ext {x : C} 
  (f : U → V) (g : V → W) {h : U → W}
   (hf : cost_at_most f x) [hg : cost_zero C g]
   (hgf : ∀ t, g (f t) = h t) : cost_at_most h x :=
cost_at_most_compose_ext hf hg (by simp) hgf

lemma cost_at_most_of_cost_zero_right {x : C} 
  {f : U → V} (g : V → W)
  (hf : cost_at_most f x) [cost_zero C g] : cost_at_most (g ∘ f) x :=
cost_at_most_of_cost_zero_right_ext f g hf (λ t, rfl)

lemma cost_at_most_of_cost_zero_wrap_ext {T : Type u}
  [cost_model C (T → U)] [cost_model C (T → W)]
  [compatible_cost_models C T U W]
  {x : C} (l : T → U) (f : U → V) (r : V → W) {g : T → W} 
  [hl : cost_zero C l] [hr : cost_zero C r] (hf : cost_at_most f x) 
  (hg : ∀ t, r (f (l t)) = g t) : cost_at_most g x :=
cost_at_most_of_cost_zero_left_ext l (r ∘ f) 
  (cost_at_most_of_cost_zero_right r hf) hg

instance cost_zero_compose (f : U → V) (g : V → W)
  [cost_zero C f] [hg : cost_zero C g] :
  cost_zero C (g ∘ f) :=
cost_at_most_of_cost_zero_left_ext f g hg (by simp)

end compatible_cost_models


class function_cost_model (C : Type) [linear_ordered_semiring C] :=
(cm (T U : Type) : cost_model C (T → U))
(cm_compatible (T U V : Type) : compatible_cost_models C T U V)
(cost_zero_id (T : Type) : cost_zero C (id : T → T))
(cost_zero_const (T : Type) {U : Type} (u : U) : cost_zero C (function.const T u))

instance function_cost_model.cost_model (C : Type)
  [linear_ordered_semiring C] [function_cost_model C] 
  (T U : Type) : cost_model C (T → U) :=
function_cost_model.cm T U 

instance function_cost_model.compatible_cost_models (C : Type)
  [linear_ordered_semiring C] [function_cost_model C]
  (T U V : Type) : compatible_cost_models C T U V :=
function_cost_model.cm_compatible T U V


namespace function_cost_model

variables [function_cost_model C]

instance cost_zero_id' (T : Type) : 
  cost_zero C (id : T → T) :=
function_cost_model.cost_zero_id T

instance cost_zero_const' (T : Type) {U : Type} (u : U) : 
  cost_zero C (λ _, u : T → U) :=
function_cost_model.cost_zero_const T u

instance cost_zero_of_subsingleton_right {T U : Type} (f : T → U)
  [hT : nonempty T] [subsingleton U] : cost_zero C f :=
begin
  by_cases hU : nonempty U,
  { exact hU.elim (λ u, cost_zero_ext (cost_zero_const T u) $ by simp) },
  { exact absurd (hT.elim (λ t, ⟨f t⟩) : nonempty U) hU }
end

instance cost_zero_of_subsingleton_left {T U : Type} (f : T → U)
  [hT : nonempty T] [subsingleton T] : cost_zero C f :=
hT.elim (λ t, cost_zero_ext (cost_zero_const T (f t)) (funext (λ t', congr_arg f (by simp))))


end function_cost_model


class pairing_cost_model (C : Type) [linear_ordered_semiring C]
  extends function_cost_model C :=
(cost_zero_fst (T U : Type) : cost_zero C (prod.fst : T × U → T))
(cost_zero_swap (T U : Type) : cost_zero C (prod.swap : T × U → U × T))
(cost_map {T T' U U' : Type} {x y : C} {f : T → T'} {g : U → U'}
  (hf : cost_at_most f x) (hg : cost_at_most g x) : 
  cost_at_most (prod.map f g) (x + y))
(cost_at_most_of_uncurry (T U V : Type) {x : C} (f : T → U → V)
  (hf : cost_at_most (function.uncurry f) x) :
  cost_at_most f x ∧ ∀ t, cost_at_most (f t) x)

namespace pairing_cost_model

variables [pairing_cost_model C]

instance cost_zero_fst' (T U : Type) :
  cost_zero C (@prod.fst T U) :=
cost_zero_fst T U

instance cost_zero_swap' (T U : Type) : 
  cost_zero C (prod.swap : T × U → U × T) :=
cost_zero_swap T U

instance cost_zero_snd (T U : Type) : 
  cost_zero C (prod.snd : T × U → U) :=
cost_zero_ext (compatible_cost_models.cost_zero_compose prod.swap prod.fst) 
  (funext $ by simp)

end pairing_cost_model


/-- Cost model on `T → M U` represents cost to evaluate at `t` and then
  'evaluate' the resulting monad (e.g. sample from the distribution of a `comp`).
  Monads that add 'non-trivial' functionality e.g. `comp.rnd`,
  will need to specify the evaluation costs of these functionalities -/
class monadic_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model C]
  (M : Type → Type u) [monad M] :=
(cm (T U : Type) : cost_model C (T → M U))
(cm_compatible (T U V : Type) : compatible_cost_models C T U (M V))
(cost_at_most_pure {T U : Type} {x : C} {f : T → U} (hf : cost_at_most f x) :
  cost_at_most (λ t, pure (f t) : T → M U) x)
(cost_at_most_bind (T U A : Type) {x y : C} {t : A → M T} {u : A → T → M U}
  (ht : cost_at_most t x) (hu : cost_at_most (function.uncurry u) y) :
  cost_at_most (λ a, bind (t a) (u a) : A → M U) (x + y))

instance monadic_cost_model.cost_model (C : Type)
  [linear_ordered_semiring C]
  [function_cost_model C]
  (M : Type → Type u) [monad M]
  [monadic_cost_model C M] (T U : Type) : cost_model C (T → M U) :=
monadic_cost_model.cm T U 

instance monadic_cost_model.compatible_cost_models (C : Type)
  [linear_ordered_semiring C]
  [function_cost_model C]
  (M : Type → Type u) [monad M]
  [monadic_cost_model C M] (T U V : Type) : 
  compatible_cost_models C T U (M V) :=
monadic_cost_model.cm_compatible T U V

namespace monadic_cost_model

variables [function_cost_model C]
  (M : Type → Type u) [monad M] [monadic_cost_model C M]

instance cost_zero_pure (T : Type) : 
  cost_zero C (pure : T → M T) :=
cost_at_most_ext (cost_at_most_pure (function_cost_model.cost_zero_id T)) le_rfl (by simp)

end monadic_cost_model

class comp_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model C]
  extends monadic_cost_model C comp :=
(cost_rnd_bitvec {n : ℕ} : cost_at_most (λ (_ : unit), comp.rnd (vector bool n)) (n : C))

namespace comp_cost_model

end comp_cost_model

class oracle_comp_cost_model (C : Type) [linear_ordered_semiring C]
  [function_cost_model C] [comp_cost_model C]
  (A B : Type) (query_cost : C)
  extends monadic_cost_model C (oracle_comp A B) :=
(cost_oc_query : cost_at_most (oracle_comp.oc_query : A → oracle_comp A B B) query_cost)
(cost_oc_ret {T U : Type} {x : C} (cu : T → comp U) (hcu : cost_at_most cu x) :
  cost_at_most (λ t, oracle_comp.oc_ret (cu t) : T → oracle_comp A B U) x)

namespace oracle_comp_cost_model

end oracle_comp_cost_model

