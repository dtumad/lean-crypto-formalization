import probability.probability_mass_function.constructions 
import data.vector.basic
import data.vector.mem
import analysis.convex.function
import analysis.convex.specific_functions

variables {α β γ : Type*}

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

lemma multiset.quot_mk_ne_zero (l : list α) (h : ¬ l.empty) :
  (l : multiset α) ≠ 0 :=
mt ((list.empty_iff_eq_nil).2 ∘ (multiset.coe_eq_zero l).1) h


open_locale nnreal ennreal classical big_operators

instance set.diagonal.decidable_pred [h : decidable_eq α] :
  decidable_pred (set.diagonal α) := λ x, h x.1 x.2

lemma real.pow_two_sum_div_le_sum_pow_two (s : finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
  (∑ x in s, f x) ^ 2 / s.card ≤ ∑ x in s, (f x) ^ 2 :=
begin
  by_cases hs : s = ∅,
  { simp only [hs, finset.sum_empty, finset.card_empty, nat.cast_zero, div_zero] },
  { have hs' : (s.card : ℝ) ≠ 0 := (nat.cast_ne_zero.2 $ λ h, hs (finset.card_eq_zero.1 h)),
    have hs'' : 0 < (s.card : ℝ) := nat.cast_pos.2 (finset.card_pos.2 $ finset.nonempty_of_ne_empty hs),
    suffices : (∑ x in s, f x / s.card) ^ 2 ≤ ∑ x in s, (f x ^ 2 / s.card),
    by rwa [← finset.sum_div, ← finset.sum_div, div_pow, pow_two (s.card : ℝ),
      ← div_div, div_le_iff hs'', div_mul, div_self hs', div_one] at this,
    have := @convex_on.map_sum_le ℝ ℝ ℝ _ _ _ _ _ _ _ (set.Ici 0) (λ x, x ^ 2) s (λ _, 1 / s.card)
      (coe ∘ f) (convex_on_pow 2) _ _ (λ i hi, set.mem_Ici.2 (hf i)),
    { simpa only [inv_mul_eq_div, one_div, algebra.id.smul_eq_mul] using this },
    { simp only [one_div, inv_nonneg, nat.cast_nonneg, implies_true_iff] },
    { simpa only [one_div, finset.sum_const, nsmul_eq_mul] using mul_inv_cancel hs' }}
end

lemma nnreal.pow_two_sum_div_le_sum_pow_two (s : finset α) (f : α → ℝ≥0) :
  (∑ x in s, f x) ^ 2 / s.card ≤ ∑ x in s, (f x) ^ 2 :=
by simpa [← nnreal.coe_le_coe, nnreal.coe_sum] using
  real.pow_two_sum_div_le_sum_pow_two s (coe ∘ f) (λ _, nnreal.coe_nonneg _)

lemma tsum_pow_two_ge_pow_two_tsum [fintype α] [topological_space ℝ≥0∞]
  (f : α → ℝ≥0∞) :
  (∑' (a : α), f a) ^ 2 / fintype.card α ≤ ∑' (a : α), (f a) ^ 2 :=
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