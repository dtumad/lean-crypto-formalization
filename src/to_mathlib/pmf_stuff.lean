import to_mathlib.general

import probability.probability_mass_function.uniform

/-!
# Lemmas about probability mass functions to move to mathlib 
-/

open_locale measure_theory nnreal ennreal big_operators

variables {α β γ : Type*}

lemma pmf.measurable_set_to_outer_measure_caratheodory (p : pmf α) (s : set α) :
  measurable_set[p.to_outer_measure.caratheodory] s :=
p.to_outer_measure_caratheodory.symm ▸ measurable_space.measurable_set_top

-- TODO: generalize to higher universes
@[simp]
lemma pmf.map_bind {α β γ : Type} (p : pmf α) (q : α → pmf β) (f : β → γ) :
  (p.bind q).map f = p.bind (λ a, (q a).map f) :=
pmf.monad_map_eq_map f (p.bind q) ▸ map_bind _

@[simp]
lemma pmf.bind_map {α β γ : Type} (p : pmf α) (f : α → β) (q : β → pmf γ) :
  (p.map f).bind q = p.bind (q ∘ f) :=
begin
  rw [pmf.map],
  rw [pmf.bind_bind],
  refine congr_arg _ _,
  refine funext (λ a, _),
  rw pmf.pure_bind,
end

@[simp]
lemma pmf.bind_const {α β : Type} (p : pmf α) (q : pmf β) :
  (p.bind $ λ _, q) = q :=
pmf.ext (λ x, by rw [pmf.bind_apply, nnreal.tsum_mul_right _ (q x), pmf.tsum_coe, one_mul])

lemma pmf.to_measure_apply_ne_top {α : Type*} [measurable_space α] (p : pmf α) (s : set α) :
  p.to_measure s ≠ ⊤ := measure_theory.measure_ne_top p.to_measure s

-- TODO: measurable??
lemma pmf.to_outer_measure_apply_ne_top {α : Type*} (p : pmf α) (s : set α) :
  p.to_outer_measure s ≠ ⊤ :=
begin
  refine λ h, (@pmf.to_measure_apply_ne_top α ⊤ p s) (le_antisymm le_top $
    le_trans (le_of_eq h.symm) (@pmf.to_outer_measure_apply_le_to_measure_apply α ⊤ p s)),
end

lemma pmf.indicator_summable {α : Type*} (p : pmf α) (s : set α)
  : summable (s.indicator p) :=
nnreal.summable_of_le (set.indicator_le_self s p) p.summable_coe

lemma pmf.apply_le_one {α : Type*} (p : pmf α) (a : α) : p a ≤ 1 :=
p.coe_le_one a

lemma pmf.to_measure_apply_eq_iff_to_outer_measure_apply_eq {α : Type*} [measurable_space α]
  (p : pmf α) (x : ℝ≥0∞) (s : set α) (hs : measurable_set s) :
  p.to_measure s = x ↔ p.to_outer_measure s = x :=
by rw [p.to_measure_apply_eq_to_outer_measure_apply s hs]

lemma pmf.to_measure_apply_Union {α : Type*} [measurable_space α] (p : pmf α)
  {f : ℕ → set α} (hf : ∀ n, measurable_set (f n)) (h : pairwise (disjoint on f)) :
  p.to_measure (⋃ n, f n) = ∑' n, p.to_measure (f n) :=
p.to_measure.m_Union hf h

lemma pmf.to_outer_measure_apply_Union {α : Type*} (p : pmf α) {f : ℕ → set α}
  (h : pairwise (disjoint on f)) : p.to_outer_measure (⋃ n, f n) = ∑' n, p.to_outer_measure (f n) :=
measure_theory.outer_measure.Union_eq_of_caratheodory _
  (λ n, pmf.measurable_set_to_outer_measure_caratheodory _ (f n)) h

lemma pmf.prod_bind_apply {α β γ : Type}
  (p : pmf (α × β)) (q : α × β → pmf γ) (c : γ) :
  p.bind q c = ∑' (a : α) (b : β), p (a, b) * q (a, b) c :=
calc p.bind q c = (∑' (x : α × β), (↑(p x * q x c) : ℝ≥0∞)).to_nnreal :
    by rw [pmf.bind_apply, ennreal.to_nnreal_tsum_coe_eq]
  ... = (∑' (a : α) (b : β), (↑(p (a, b) * q (a, b) c) : ℝ≥0∞)).to_nnreal :
    congr_arg ennreal.to_nnreal (tsum_prod' ennreal.summable (λ _, ennreal.summable))
  ... = ∑' (a : α), (∑' (b : β), (↑(p (a, b) * q (a, b) c) : ℝ≥0∞)).to_nnreal :
    begin
      refine ennreal.tsum_to_nnreal_eq (λ a, _),
      have : ∑' (b : β), (↑(p (a, b) * q (a, b) c) : ℝ≥0∞) ≤ p.bind q c,
      {

        rw [pmf.bind_apply, ennreal.coe_tsum],
        {
          refine tsum_le_tsum_of_inj (λ b, (a, b)) _ _ (λ _, le_rfl) ennreal.summable ennreal.summable,
          refine (λ a' b' h, (prod.eq_iff_fst_eq_snd_eq.1 h).2),
          intros x hx,
          refine zero_le',
        },
        have := pmf.summable_coe p,
        refine nnreal.summable_of_le (λ x, _) this,
        refine le_trans _ (le_of_eq $ (mul_one $ p x)),
        refine mul_le_mul' le_rfl ((q x).coe_le_one c),
      },
      {
        refine ne_of_lt (lt_of_le_of_lt _ ennreal.one_lt_top),
        refine le_trans this _,
        refine ennreal.coe_le_one_iff.2 _,
        refine (p.bind q).coe_le_one c,
      }
    end
  ... = ∑' (a : α) (b : β), p (a, b) * q (a, b) c :
    begin
      refine tsum_congr (λ a, _),
      refine ennreal.tsum_to_nnreal_eq (λ b, _),
      refine ne_of_lt _,
      refine lt_of_le_of_lt _ ennreal.one_lt_top,
      rw ennreal.coe_le_one_iff,
      suffices : p (a, b) * q (a, b) c ≤ 1 * 1,
      by rwa [mul_one] at this,
      refine mul_le_mul _ _ zero_le' zero_le',
      refine pmf.coe_le_one _ _,
      refine pmf.coe_le_one _ _,
    end

lemma pmf.map_fst_apply {α β : Type*} (p : pmf (α × β)) (a : α) :
  p.map prod.fst a = ∑' (b : β), p (a, b) :=
begin
  rw [pmf.map_apply],
  sorry,
end


-- lemma pmf.to_outer_measure_apply_image {α : Type*} (p : pmf β) (e : set α) (f : α → β) :
--   p.to_outer_measure (f '' e) = 

-- lemma pmf.indicator_map {α : Type*} (p : pmf α) (f : α → β) (e : set β) :
