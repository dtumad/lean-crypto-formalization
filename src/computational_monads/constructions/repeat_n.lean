import data.vector.basic

import computational_monads.oracle_comp
import computational_monads.distribution_semantics.eval_distribution

namespace oracle_comp

open oracle_spec

variables {A B : Type} {spec : oracle_spec}
  (oa : oracle_comp spec A) (n : ℕ)

def repeat_n (oa : oracle_comp spec A) : Π (n : ℕ), oracle_comp spec (vector A n)
| 0 := return vector.nil
| (n + 1) := do { a ← oa, as ← repeat_n n, return (a ::ᵥ as) }

@[simp]
lemma repeat_n_apply_zero :
  repeat_n oa 0 = return vector.nil :=
rfl

@[simp]
lemma repeat_n_apply_succ :
  repeat_n oa (n + 1) = do { a ← oa, as ← repeat_n oa n, return (a ::ᵥ as) } :=
rfl

@[simp]
lemma support_repeat_n (oa : oracle_comp spec A) :
  Π n, support (repeat_n oa n) = { v | ∀ a ∈ v.to_list, a ∈ oa.support }
| 0 := begin
  ext v,
  simp only [repeat_n_apply_zero, support_pure, set.mem_singleton_iff,
    eq_iff_true_of_subsingleton, set.mem_set_of_eq, true_iff],
  exact λ a ha, false.elim (vector.not_mem_to_list_of_length_zero v a ha),
end
| (n + 1) := begin
  sorry
end

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