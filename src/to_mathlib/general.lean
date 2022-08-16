import probability.probability_mass_function.constructions 
import data.vector.basic
import data.vector.mem
import analysis.convex.function
import analysis.convex.specific_functions

variables {α β γ : Type*}

open_locale measure_theory

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

lemma multiset.quot_mk_ne_zero (l : list α) (h : ¬ l.empty) :
  (l : multiset α) ≠ 0 :=
mt ((list.empty_iff_eq_nil).2 ∘ (multiset.coe_eq_zero l).1) h

open_locale nnreal ennreal classical big_operators

lemma pmf.measurable_set_to_outer_measure_caratheodory (p : pmf α) (s : set α) :
  measurable_set[p.to_outer_measure.caratheodory] s :=
begin
  convert measurable_space.measurable_set_top,
  exact (pmf.to_outer_measure_caratheodory p),
end

instance set.diagonal.mem_decidable [h : decidable_eq α] (x : α × α) :
  decidable (x ∈ set.diagonal α) := h x.1 x.2

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

section pmf

section apply_eq_one

lemma nnreal.sum_le_tsum {α : Type} {f : α → ℝ≥0} (hf : summable f) (s : finset α) :
  ∑ x in s, f x ≤ ∑' x, f x :=
by simpa only [← ennreal.coe_le_coe, ennreal.coe_tsum hf, ennreal.coe_finset_sum] 
  using ennreal.sum_le_tsum s

lemma pmf.apply_eq_one_iff {A : Type} (p : pmf A) (a : A) :
  p a = 1 ↔ p.support = {a} :=
begin
  refine ⟨λ h, set.eq_of_subset_of_subset _ _, λ h, le_antisymm (pmf.coe_le_one p a) (le_of_eq _)⟩,
  { refine λ a' ha', by_contradiction (λ h', false.elim (ne_of_gt _ p.tsum_coe)),
    have : a ∉ {a'} := finset.not_mem_singleton.2 (ne.symm h'),
    calc 1 < p a + p a' : lt_add_of_le_of_pos (le_of_eq h.symm)
        (lt_of_le_of_ne (nnreal.coe_nonneg $ p a') (ha'.symm))
      ... ≤ ∑ x in {a, a'}, p x : by rw [finset.sum_insert this, finset.sum_singleton]
      ... ≤ ∑' (x : A), p x : nnreal.sum_le_tsum p.summable_coe {a, a'} },
  { intros a' ha',
    rw [set.mem_singleton_iff.1 ha', pmf.mem_support_iff, h],
    exact one_ne_zero },
  { refine trans (p.tsum_coe).symm (trans (tsum_congr $ λ a', _) (tsum_ite_eq a _)),
    split_ifs with haa',
    { rw haa' },
    { rwa [pmf.apply_eq_zero_iff p, h, set.mem_singleton_iff] } }
end

end apply_eq_one

@[simp]
lemma pmf.map_bind' {A B C : Type} (p : pmf A) (q : A → pmf B) (f : B → C) :
  (p >>= q).map f = p >>= (λ a, (q a).map f) :=
begin
  erw [pmf.map, pmf.bind_bind],
  refine congr_arg _ (funext $ λ a, _),
  rw pmf.bind_pure_comp,
end

@[simp]
lemma pmf.map_bind {A B C : Type} (p : pmf A) (q : A → pmf B) (f : B → C) :
  f <$> (p >>= q) = p >>= λ a, (f <$> (q a)) :=
begin
  refine (pmf.map_bind' p q f),
end

@[simp]
lemma pmf.bind_const {A B : Type} (p : pmf A) (q : pmf B) :
  (p >>= λ _, q) = q :=
begin
  ext x,
  simp [has_bind.bind, (nnreal.tsum_mul_right _ (q x))]
end


end pmf