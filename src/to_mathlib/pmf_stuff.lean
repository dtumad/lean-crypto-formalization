/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import to_mathlib.sums
import probability.probability_mass_function.uniform

/-!
# Lemmas about probability mass functions to move to mathlib 
-/

open_locale measure_theory nnreal ennreal big_operators classical

variables {α β γ : Type*}

lemma pmf.measurable_set_to_outer_measure_caratheodory (p : pmf α) (s : set α) :
  measurable_set[p.to_outer_measure.caratheodory] s :=
p.to_outer_measure_caratheodory.symm ▸ measurable_space.measurable_set_top

lemma pmf.indicator_summable {α : Type*} (p : pmf α) (s : set α)
  : summable (s.indicator p) :=
nnreal.summable_of_le (set.indicator_le_self s p) p.summable_coe

section monad

@[simp]
lemma pmf.map_bind {α β γ : Type*} (p : pmf α) (q : α → pmf β) (f : β → γ) :
  (p.bind q).map f = p.bind (λ a, (q a).map f) :=
by simp_rw [pmf.map, pmf.bind_bind]

@[simp]
lemma pmf.bind_map {α β γ : Type*} (p : pmf α) (f : α → β) (q : β → pmf γ) :
  (p.map f).bind q = p.bind (q ∘ f) :=
begin
  rw [pmf.map],
  rw [pmf.bind_bind],
  refine congr_arg _ _,
  refine funext (λ a, _),
  rw pmf.pure_bind,
end

@[simp]
lemma pmf.bind_const {α β : Type*} (p : pmf α) (q : pmf β) :
  (p.bind $ λ _, q) = q :=
pmf.ext (λ x, by rw [pmf.bind_apply, nnreal.tsum_mul_right _ (q x), pmf.tsum_coe, one_mul])

end monad

section measure

lemma pmf.to_measure_apply_ne_top {α : Type*} [measurable_space α] (p : pmf α) (s : set α) :
  p.to_measure s ≠ ⊤ := measure_theory.measure_ne_top p.to_measure s

-- TODO: measurable??
lemma pmf.to_outer_measure_apply_ne_top {α : Type*} (p : pmf α) (s : set α) :
  p.to_outer_measure s ≠ ⊤ :=
begin
  refine λ h, (@pmf.to_measure_apply_ne_top α ⊤ p s) (le_antisymm le_top $
    le_trans (le_of_eq h.symm) (@pmf.to_outer_measure_apply_le_to_measure_apply α ⊤ p s)),
end

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

end measure

section prod

/-- If and intermediate distribution is a product, can express the probability as a
double sum rather than a sum over a `prod` type. -/
lemma pmf.prod_bind_apply {α β γ : Type*}
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



/-- Alternative to `prod_bind_apply` with the opposite order of summation -/
lemma pmf.prod_bind_apply' {α β γ : Type*}
  (p : pmf (α × β)) (q : α × β → pmf γ) (c : γ) :
  p.bind q c = ∑' (b : β) (a : α), p (a, b) * q (a, b) c :=
begin
  let p' : pmf (β × α) := p.map prod.swap,
  let q' : β × α → pmf γ := q ∘ prod.swap,
  have : p.bind q = (p.map prod.swap).bind (q ∘ prod.swap) := begin
    -- ext x,
    rw [pmf.bind_map p prod.swap],
    rw [function.comp.assoc],
    rw [prod.swap_swap_eq],
    rw [function.comp.right_id]
  end,
  rw this,

  refine (pmf.prod_bind_apply _ _ c).trans _,
  refine tsum_congr (λ b, _),
  refine tsum_congr (λ a, _),
  rw [function.comp_app, prod.swap_prod_mk],
  have : (pmf.map prod.swap p) (b, a) = p (a, b) := begin
    rw [pmf.map_apply],
    refine trans (tsum_eq_single (a, b) _) _,
    {
      intros x hx,
      have : (b, a) ≠ x.swap := λ hx', hx _,
      simp only [this, if_false],
      refine trans _ (trans (congr_arg prod.swap hx'.symm) rfl),
      refine symm (prod.swap_swap x)
    },
    { rw [prod.swap_prod_mk, eq_self_iff_true, if_true] }
  end,
  rw this,
end

/-- First output of a computation of a `prod` type as a summation over possible second outputs. -/
lemma pmf.map_fst_apply {α β : Type*} (p : pmf (α × β)) (a : α) :
  p.map prod.fst a = ∑' (b : β), p (a, b) :=
calc p.map prod.fst a = ∑' (a' : α) (b : β), ite (a = a') (p (a', b)) 0 :
    by simp_rw [pmf.map, pmf.prod_bind_apply p, function.comp_apply,
      pmf.pure_apply, mul_ite, mul_one, mul_zero]
  ... = ∑' (b : β), ite (a = a) (p (a, b)) 0 :
    tsum_eq_single _ (λ a' ha', by simp only [ne.symm ha', if_false, tsum_zero])
  ... = ∑' (b : β), p (a, b) : by simp only [eq_self_iff_true, if_true]

/-- Second output of a computation of a `prod` type as a summation over possible first outputs. -/
lemma pmf.map_snd_apply {α β : Type*} (p : pmf (α × β)) (b : β) :
  p.map prod.snd b = ∑' (a : α), p (a, b) :=
calc p.map prod.snd b = ∑' (b' : β) (a : α), ite (b = b') (p (a, b')) 0 :
    by simp_rw [pmf.map, pmf.prod_bind_apply' p, function.comp_apply,
      pmf.pure_apply, mul_ite, mul_one, mul_zero]
  ... = ∑' (a : α), ite (b = b) (p (a, b)) 0 :
    tsum_eq_single _ (λ a' ha', by simp only [ne.symm ha', if_false, tsum_zero])
  ... = ∑' (a : α), p (a, b) : by simp only [eq_self_iff_true, if_true]


end prod