import computational_complexity.cost_model
import data.vector2

open cost_model

variables {C : Type} [ordered_semiring C]
  [function_cost_model C]

class pairing_cost_extension (C : Type) [ordered_semiring C]
  [function_cost_model C] :=
(cost_zero_fst (T U : Type) : cost_zero C (prod.fst : T × U → T))
(cost_zero_swap (T U : Type) : cost_zero C (prod.swap : T × U → U × T))
(cost_zero_pair_unit (T : Type) : cost_zero C (λ (t : T), (t, ())))
(cost_at_most_prod_map {T T' U U' : Type} {x y : C} {f : T → T'} {g : U → U'}
  (hf : cost_at_most f x) (hg : cost_at_most g y) : 
  cost_at_most (prod.map f g) (x + y))
(cost_at_most_of_uncurry (T U V : Type) {x : C} (f : T → U → V)
  (hf : cost_at_most (function.uncurry f) x) :
  cost_at_most f x ∧ ∀ t, cost_at_most (f t) x)

namespace pairing_cost_extension

variable [pairing_cost_extension C]

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

lemma cost_at_most_prod_map_of_le {T T' U U' : Type} {x y z : C}
  {f : T → T'} {g : U → U'} (hf : cost_at_most f x) (hg : cost_at_most g y)
  (hxyz : x + y ≤ z) : cost_at_most (prod.map f g) z :=
cost_model.cost_trans (cost_at_most_prod_map hf hg) hxyz

lemma cost_at_most_prod_map_of_cost_zero_left {T T' U U' : Type} {x : C}
  (f : T → T') {g : U → U'} [hf : cost_zero C f] (hg : cost_at_most g x) :
  cost_at_most (prod.map f g) x :=
cost_at_most_prod_map_of_le hf hg (by simp)

lemma cost_at_most_prod_map_of_cost_zero_right {T T' U U' : Type} {x : C}
  {f : T → T'} (g : U → U') (hf : cost_at_most f x) [hg : cost_zero C g] :
  cost_at_most (prod.map f g) x :=
cost_at_most_prod_map_of_le hf hg (by simp)

instance cost_zero_prod_map {T T' U U' : Type}
  (f : T → T') (g : U → U') [hf : cost_zero C f] [hg : cost_zero C g] :
  cost_zero C (prod.map f g) :=
cost_at_most_prod_map_of_cost_zero_left f hg

instance cost_zero_pair_const (T : Type) {U : Type} (u : U) :
  cost_zero C (λ (t : T), (t, u)) :=
compatible_cost_models.cost_at_most_of_cost_zero_right_ext
    (λ (t : T), (t, ())) (prod.map id (function.const unit u))
    (cost_zero_pair_unit T) (by simp)

instance cost_zero_const_pair {T : Type} (t : T) (U : Type) :
  cost_zero C (λ (u : U), (t, u)) :=
compatible_cost_models.cost_zero_compose_ext
  (λ (u : U), (u, t)) (prod.swap) (by simp)

end pairing_cost_extension

-- TODO: Could decide to derive these from some cost model on sigma types?
-- TODO: These might look cleaner if cost_at_most had it's arguments swapped
class vector_cost_extension (C : Type) [ordered_semiring C]
  [function_cost_model C] :=
(cost_one_vector_cons (T : Type) (n : ℕ) : cost_at_most
  (function.uncurry vector.cons : T × vector T n → vector T n.succ) (1 : C))
(cost_at_most_nth (T : Type) (n : ℕ) : cost_at_most
  (function.uncurry vector.nth : vector T n × fin n → T) (n : C))

namespace vector_cost_extension

variable [vector_cost_extension C]

end vector_cost_extension
