import probability.probability_mass_function.constructions 
import data.vector.basic
import data.vector.mem
import analysis.convex.function
import analysis.convex.specific_functions

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

open_locale measure_theory nnreal ennreal classical big_operators

variables {α β γ : Type*}

section list_like

lemma multiset.quot_mk_ne_zero (l : list α) (hl : ¬ l.empty) : ↑l ≠ (0 : multiset α) :=
mt ((list.empty_iff_eq_nil).2 ∘ (multiset.coe_eq_zero l).1) hl

lemma vector.to_list_nonempty {n : ℕ} (v : vector α (n + 1)) : ¬ v.to_list.empty :=
match v with
| ⟨a :: as, _⟩ := by simp
end

lemma finset.to_list_nonempty {A : Type} (s : finset A) (hs : s.nonempty) : ¬ s.to_list.empty :=
let ⟨x, hx⟩ := hs in
  λ h', list.not_mem_nil x ((list.empty_iff_eq_nil.1 h') ▸ (finset.mem_to_list s).2 hx)

lemma list.drop_succ_cons {A : Type} (as : list A) (a : A) (n : ℕ) :
  (a :: as).drop (n + 1) = as.drop n :=
rfl

lemma vector.not_mem_of_length_zero {A : Type} (v : vector A 0) (a : A) :
  a ∉ v.to_list :=
(vector.eq_nil v).symm ▸ id

end list_like

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

lemma ennreal.pow_sum_div_card_le_sum_pow (s : finset α) (f : α → ℝ≥0∞) (n : ℕ) :
  (∑ x in s, f x) ^ (n + 1) / s.card ^ n ≤ ∑ x in s, (f x) ^ (n + 1) :=
begin
  sorry
end

section prod

lemma set.not_mem_prod {α β : Type} {s : set α} {t : set β} {x : α × β} :
  x ∉ s ×ˢ t ↔ x.1 ∉ s ∨ x.2 ∉ t :=
not_and_distrib

instance set.decidable_mem_prod {α β : Type} (s : set α) (t : set β)
  [hs : decidable_pred s] [ht : decidable_pred t] (x : α × β) : decidable (x ∈ s ×ˢ t) :=
match hs x.1 with
| is_true ha := match ht x.2 with
  | is_true hb := is_true (set.mem_prod.2 ⟨ha, hb⟩)
  | is_false hb := is_false (set.not_mem_prod.2 $ or.inr hb)
  end
| is_false ha := is_false (set.not_mem_prod.2 $ or.inl ha)
end

end prod