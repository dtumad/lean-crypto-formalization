import data.vector.basic

import computational_monads.oracle_comp
import computational_monads.distribution_semantics.eval_distribution

namespace oracle_comp

open oracle_spec

variables {A B : Type} {spec : oracle_spec}

def repeat_n : Π (oa : oracle_comp spec A) (n : ℕ), oracle_comp spec (vector A n)
| _ 0 := return vector.nil
| oa (n + 1) := do {
  a ← oa,
  as ← repeat_n oa n,
  return (a ::ᵥ as)
}

@[simp]
lemma support_repeat_n (oa : oracle_comp spec A) (n : ℕ) :
  support (repeat_n oa n) = { v | ∀ a ∈ v.to_list, a ∈ oa.support } :=
sorry

lemma mem_support_of_mem_of_support_repeat_n (oa : oracle_comp spec A) (n : ℕ)
  (v : vector A n) (hv : v ∈ (repeat_n oa n).support) (a : A) (ha : a ∈ v.to_list) :
  a ∈ oa.support :=
sorry

/-- Probability of a vector is the product of probabilities of each element. -/
@[simp]
lemma eval_distribution_repeat_n_apply [spec.finite_range]
  (oa : oracle_comp spec A) (n : ℕ) (v : vector A n) :
  ⟦repeat_n oa n⟧ v = (v.map (λ a, ⟦oa⟧ a)).to_list.prod  :=
sorry

end oracle_comp