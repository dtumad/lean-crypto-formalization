import probability.probability_mass_function.constructions 
import data.vector.basic
import data.vector.mem
import analysis.convex.function
import analysis.convex.specific_functions

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

open_locale measure_theory nnreal ennreal classical big_operators

variables {α β γ : Type*} {n : ℕ}

lemma tsum_eq_sum_univ {α β : Type*} [fintype α] [topological_space β]
  [add_comm_monoid β] [t2_space β] (f : α → β) :
  ∑' (x : α), f x = ∑ x, f x :=
tsum_eq_sum (λ b hb, false.elim (hb $ finset.mem_univ b))

-- TODO: PR opened for this
section list_like

lemma multiset.quot_mk_ne_zero (l : list α) (hl : ¬ l.empty) : ↑l ≠ (0 : multiset α) :=
mt ((list.empty_iff_eq_nil).2 ∘ (multiset.coe_eq_zero l).1) hl

@[simp] lemma vector.empty_to_list_eq_ff (v : vector α (n + 1)) : v.to_list.empty = ff :=
match v with | ⟨a :: as, _⟩ := rfl end

@[simp] lemma vector.to_list_nonempty (v : vector α (n + 1)) : ¬ v.to_list.empty :=
by simp only [vector.empty_to_list_eq_ff, coe_sort_ff, not_false_iff]

lemma finset.to_list_nonempty {A : Type} (s : finset A) (hs : s.nonempty) : ¬ s.to_list.empty :=
let ⟨x, hx⟩ := hs in λ h', list.not_mem_nil x (list.empty_iff_eq_nil.1 h' ▸ s.mem_to_list.2 hx)

end list_like

-- NOTE: Pull request opened for this
section sums

lemma real.pow_sum_div_card_le_sum_pow (s : finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (n : ℕ) :
  (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, (f x) ^ (n + 1) :=
begin
  by_cases hs : s = ∅,
  { simp only [hs, finset.sum_empty, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_div] },
  { have hs₀ : s.card ≠ 0 := hs ∘ finset.card_eq_zero.1,
    have hs' : (s.card : ℝ) ≠ 0 := (nat.cast_ne_zero.2 hs₀),
    have hs'' : 0 < (s.card : ℝ) := nat.cast_pos.2 (nat.pos_of_ne_zero hs₀),
    suffices : (∑ x in s, f x / s.card) ^ (n + 1) ≤ ∑ x in s, (f x ^ (n + 1) / s.card),
    by rwa [← finset.sum_div, ← finset.sum_div, div_pow, pow_succ' (s.card : ℝ),
        ← div_div, div_le_iff hs'', div_mul, div_self hs', div_one] at this,
    have := @convex_on.map_sum_le ℝ ℝ ℝ _ _ _ _ _ _ _ (set.Ici 0) (λ x, x ^ (n + 1)) s
      (λ _, 1 / s.card) (coe ∘ f) (convex_on_pow (n + 1)) _ _ (λ i hi, set.mem_Ici.2 (hf i)),
    { simpa only [inv_mul_eq_div, one_div, algebra.id.smul_eq_mul] using this },
    { simp only [one_div, inv_nonneg, nat.cast_nonneg, implies_true_iff] },
    { simpa only [one_div, finset.sum_const, nsmul_eq_mul] using mul_inv_cancel hs' }}
end

lemma nnreal.pow_sum_div_card_le_sum_pow (s : finset α) (f : α → ℝ≥0) (n : ℕ) :
  (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, (f x) ^ (n + 1) :=
by simpa [← nnreal.coe_le_coe, nnreal.coe_sum] using
  real.pow_sum_div_card_le_sum_pow s (coe ∘ f) (λ _, nnreal.coe_nonneg _) n

end sums

section ennreal

lemma ennreal.to_nnreal_eq_one_iff (x : ℝ≥0∞) : x.to_nnreal = 1 ↔ x = 1 :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  cases x,
  { exact false.elim (zero_ne_one $ ennreal.top_to_nnreal.symm.trans h) },
  { exact congr_arg _ h }
end

lemma ennreal.to_nnreal_tsum_eq {α : Type*} {f : α → ℝ≥0∞} (hf : ∀ x, f x ≠ ⊤) :
  (∑' x, (f x)).to_nnreal = ∑' x, (f x).to_nnreal :=
calc (∑' x, (f x)).to_nnreal
  = (∑' x, (f x).to_nnreal : ℝ≥0∞).to_nnreal :
    congr_arg ennreal.to_nnreal (tsum_congr $ λ x, (ennreal.coe_to_nnreal (hf x)).symm)
  ... = ∑' x, (f x).to_nnreal : by rw [nnreal.tsum_eq_to_nnreal_tsum]

lemma ennreal.to_nnreal_eq_to_nnreal_iff (x y : ℝ≥0∞) :
  x.to_nnreal = y.to_nnreal ↔ x = y ∨ (x = 0 ∧ y = ⊤) ∨ (x = ⊤ ∧ y = 0) :=
begin
  cases x,
  { simp only [@eq_comm ℝ≥0 0 y.to_nnreal, @eq_comm ℝ≥0∞ _ y, ennreal.to_nnreal_eq_zero_iff,
      ennreal.none_eq_top, ennreal.top_to_nnreal, ennreal.top_ne_zero, false_and, eq_self_iff_true,
        true_and, false_or, or_comm (y = ⊤)] },
  { cases y; simp }
end

lemma ennreal.to_nnreal_eq_to_nnreal_iff' (x y : ℝ≥0∞) (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
  x.to_nnreal = y.to_nnreal ↔ x = y :=
by simp only [ennreal.to_nnreal_eq_to_nnreal_iff x y, hx, hy, and_false, false_and, or_false]

end ennreal