import computational_monads.oracle_access.oracle_comp
import computational_monads.probabalistic_computation.constructions
import computational_complexity.polynomial_asymptotics
 
/-!
# Cost Model for shallow embedding

This file defines an extensible cost model for lean fucntions,
  as well as functions extended with `prob_comp` or `oracle_comp A B` monads.
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
* `comp_cost_model` → `cost_model C (T → prob_comp U)`
* `oracle_comp_cost_model A B` → `cost_model C (T → oracle_comp A B U)`

The cost model on a function `f : T → U` represents the cost of evaluating `f` on an arbitrary input.
For a function of the form `f : T → prob_comp U`, it represents the cost of evaluating `f` on an input,
  and sampling some `U` from the resulting `prob_comp U`.

-/

universes u v w

/-- Cost model on a type `T` where cost takes values in `C`. -/
class cost_model (C : Type) (T : Type v) [ordered_semiring C] :=
(cost_pred : T → C → Prop)
(cost_trans {x y : C} {t : T} : cost_pred t x → x ≤ y → cost_pred t y)
(nonneg_of_has_cost {x : C} {t : T} : cost_pred t x → 0 ≤ x)

variables {C : Type} [ordered_semiring C] {T : Type u}

namespace cost_model

def cost_at_most {T : Type u} {C : Type} [ordered_semiring C]
  [cost_model C T] (t : T) (x : C) : Prop :=
cost_model.cost_pred t x

@[class]
def cost_zero (C : Type) {T : Type u} [ordered_semiring C]
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

lemma cost_zero_of_le [cost_model C T] {t : T} {c : C}
  (ht : cost_at_most t c) (hc : c ≤ 0) : cost_zero C t :=
cost_trans ht hc

end cost_model


open cost_model

class compatible_cost_models (C : Type) [ordered_semiring C]
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

lemma cost_zero_compose_ext (f : U → V) (g : V → W) {h : U → W}
  [hf : cost_zero C f] [hg : cost_zero C g]
  (hfg : ∀ u, g (f u) = h u) : cost_zero C h :=
cost_at_most_of_cost_zero_left_ext f g hg hfg

instance cost_zero_compose (f : U → V) (g : V → W)
  [cost_zero C f] [hg : cost_zero C g] :
  cost_zero C (g ∘ f) :=
cost_zero_compose_ext f g (by simp)

end compatible_cost_models

class function_cost_model (C : Type) [ordered_semiring C] :=
(cm (T U : Type) : cost_model C (T → U))
(cm_compatible (T U V : Type) : compatible_cost_models C T U V)
(cost_zero_id (T : Type) : cost_zero C (id : T → T))
(cost_zero_const (T : Type) {U : Type} (u : U) : cost_zero C (function.const T u))

instance function_cost_model.cost_model (C : Type)
  [ordered_semiring C] [function_cost_model C] 
  (T U : Type) : cost_model C (T → U) :=
function_cost_model.cm T U 

instance function_cost_model.compatible_cost_models (C : Type)
  [ordered_semiring C] [function_cost_model C]
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
hT.elim (λ t, cost_zero_ext (cost_zero_const T $ f t) $ by simp)

instance cost_zero_of_subsingleton_left {T U : Type} (f : T → U)
  [hT : nonempty T] [subsingleton T] : cost_zero C f :=
hT.elim (λ t, cost_zero_ext (cost_zero_const T $ f t) (funext (λ t', congr_arg f (by simp))))

end function_cost_model

-- TODO: Does this make any sense?
class test_cost_model (C : Type) [ordered_semiring C]
  [function_cost_model C] (M : Type → Type u) [monad M] :=
(cm (T U : Type) : cost_model C (reader_t T M U))

/-- Cost model on `T → M U` represents cost to evaluate at `t` and then
  'evaluate' the resulting monad (e.g. sample from the distribution of a `prob_comp`).
  Monads that add 'non-trivial' functionality e.g. `prob_comp.rnd`,
  will need to specify the evaluation costs of these functionalities -/
class monadic_cost_model (C : Type) [ordered_semiring C]
  [function_cost_model C]
  (M : Type → Type u) [monad M] :=
(cm (T U : Type) : cost_model C (T → M U))
(cm_compatible (T U V : Type) : compatible_cost_models C T U (M V))
(cost_zero_pure (T : Type) : cost_zero C (pure : T → M T))
(cost_at_most_bind {T U V : Type} {x y : C} {mu : T → M U} {mv : T → U → M V}
  (hmu : cost_at_most mu x) (hmv : cost_at_most (function.uncurry mv) y) :
  cost_at_most (λ a, bind (mu a) (mv a) : T → M V) (x + y))

instance monadic_cost_model.cost_model (C : Type) [ordered_semiring C]
  [function_cost_model C] (M : Type → Type u) [monad M] [monadic_cost_model C M] 
  (T U : Type) : cost_model C (T → M U) :=
monadic_cost_model.cm T U 

instance monadic_cost_model.compatible_cost_models (C : Type) [ordered_semiring C]
  [function_cost_model C] (M : Type → Type u) [monad M] [monadic_cost_model C M] 
  (T U V : Type) : compatible_cost_models C T U (M V) :=
monadic_cost_model.cm_compatible T U V

namespace monadic_cost_model

variables [function_cost_model C]
  (M : Type → Type u) [monad M] [monadic_cost_model C M]

instance cost_zero_pure' (T : Type) : 
  cost_zero C (pure : T → M T) :=
monadic_cost_model.cost_zero_pure T

instance cost_zero_return (T : Type) :
  cost_zero C (return : T → M T) :=
monadic_cost_model.cost_zero_pure' M T

lemma cost_at_most_pure {T U : Type} {x : C} {f : T → U} (hf : cost_at_most f x) :
  cost_at_most (pure ∘ f : T → M U) x :=
compatible_cost_models.cost_at_most_of_cost_zero_right pure hf

variable {M}

instance cost_zero_bind {T U V : Type}
  {mu : T → M U} {mv : T → U → M V}
  [hmu : cost_zero C mu] [hmv : cost_zero C (function.uncurry mv)] :
  cost_zero C (λ a, bind (mu a) (mv a)) :=
cost_zero_of_le (cost_at_most_bind hmu hmv) (le_of_eq (add_zero 0))

lemma cost_at_most_bind_of_le {T U V : Type} {x y z : C}
  {mu : T → M U} {mv : T → U → M V}
  (hmu : cost_at_most mu x) (hmv : cost_at_most (function.uncurry mv) y)
  (hxyz : x + y ≤ z) : cost_at_most (λ a, bind (mu a) (mv a)) z :=
cost_model.cost_trans (monadic_cost_model.cost_at_most_bind hmu hmv) hxyz

end monadic_cost_model

/-- Implement a specific monadic cost model for `prob_comp`. 
  Sampling random bits is defined to have unit cost.
  Extensionality makes this behave more like the function cost model,
  so that the cost model is a fact about the behaviour not the algorithm -/
class comp_cost_model (C : Type) [ordered_semiring C]
  [function_cost_model C]
  extends monadic_cost_model C prob_comp :=
(cost_at_most_comp_ext {T U : Type} {ct ct' : U → prob_comp T} {c : C}
  (h : ∀ u, (ct u).eval_distribution = (ct' u).eval_distribution)
  (hct : cost_at_most ct c) : cost_at_most ct' c)

instance comp_cost_model.cost_model {C : Type} [ordered_semiring C]
  [function_cost_model C] [comp_cost_model C]
  (T U : Type) : cost_model C (T → prob_comp U) :=
monadic_cost_model.cost_model C prob_comp T U

instance comp_cost_model.compatible_cost_models {C : Type} [ordered_semiring C]
  [function_cost_model C] [comp_cost_model C]
  (T U V : Type) : compatible_cost_models C T U (prob_comp V) :=
monadic_cost_model.compatible_cost_models C prob_comp T U V

instance comp_cost_model.cost_zero_ret [function_cost_model C]
  [comp_cost_model C] (T : Type) : 
  cost_zero C (return : T → prob_comp T) :=
monadic_cost_model.cost_zero_pure' prob_comp T

namespace comp_cost_model

variables [function_cost_model C] [comp_cost_model C]

lemma cost_at_most_comp_ext_iff {T U : Type} {ct ct' : U → prob_comp T}
  (h : ∀ u, (ct u).eval_distribution = (ct' u).eval_distribution)
  (c : C) : cost_at_most ct c ↔ cost_at_most ct' c :=
⟨comp_cost_model.cost_at_most_comp_ext h,
  comp_cost_model.cost_at_most_comp_ext (λ u, eq.symm $ h u)⟩

lemma cost_at_most_comp_ret {T U : Type} {x : C} {f : T → U}
  (hf : cost_at_most f x) : cost_at_most (return ∘ f : T → prob_comp U) x :=
monadic_cost_model.cost_at_most_pure prob_comp hf

lemma cost_at_most_comp_bind {T U V : Type} {x y : C} 
  {cu : T → prob_comp U} {cv : T → U → prob_comp V}
  (hcu : cost_at_most cu x) (hcv : cost_at_most (function.uncurry cv) y) :
  cost_at_most (λ t, (cu t) >>= (cv t)) (x + y) :=
monadic_cost_model.cost_at_most_bind hcu hcv

lemma cost_at_most_comp_bind_of_le {T U V : Type} {x y z : C}
  {cu : T → prob_comp U} {cv : T → U → prob_comp V}
  (hcu : cost_at_most cu x) (hcv : cost_at_most (function.uncurry cv) y)
  (hxyz : x + y ≤ z) : cost_at_most (λ t, (cu t) >>= (cv t)) z :=
monadic_cost_model.cost_at_most_bind_of_le hcu hcv hxyz

end comp_cost_model

class oracle_comp_cost_model (C : Type) [ordered_semiring C]
  [function_cost_model C] [comp_cost_model C]
  (spec : oracle_comp_spec)
  extends monadic_cost_model C (oracle_comp spec) :=
(cost_oc_query {i : spec.ι} : 
  cost_at_most (oracle_comp.oc_query i) (1 : C))
(cost_oc_ret {T U : Type} {x : C} (cu : T → prob_comp U) (hcu : cost_at_most cu x) :
  cost_at_most (λ t, oracle_comp.oc_ret (cu t) : T → oracle_comp spec U) x)

instance oracle_comp_cost_model.cost_model {C : Type} [ordered_semiring C]
  [function_cost_model C] [comp_cost_model C]
  (spec : oracle_comp_spec) 
  [oracle_comp_cost_model C spec] (T U : Type) :
  cost_model C (T → oracle_comp spec U) :=
monadic_cost_model.cost_model C (oracle_comp spec) T U

instance oracle_comp_cost_model.cost_zero_oc_ret {C : Type} [ordered_semiring C]
  [function_cost_model C] [comp_cost_model C]
  (spec : oracle_comp_spec) [oracle_comp_cost_model C spec]
  (T : Type) : cost_zero C (oracle_comp.oc_ret ∘ return : T → oracle_comp spec T) :=
monadic_cost_model.cost_zero_pure' (oracle_comp spec) T

namespace oracle_comp_cost_model



end oracle_comp_cost_model

