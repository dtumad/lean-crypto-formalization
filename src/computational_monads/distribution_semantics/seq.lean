/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.distribution_semantics.tactics.push_map_dist_equiv

/-!
# Distribution Semantics of Sequence Operation

This file contains lemmas about the distribution semantics of `<*>`, which can be use
to combine two computations with some operation.
For example given `oa ob : oracle_comp spec ℕ`, `(+) <$> oa <*> ob` is the computation that
runs `oa` and `ob` independently to get `x` and `y`, returning the sum `x + y`.
-/

namespace oracle_comp

open oracle_spec
open_locale ennreal big_operators

variables {α β γ δ : Type} {spec spec' : oracle_spec}

section seq

variables (og : oracle_comp spec (α → β)) (oa : oracle_comp spec α)

@[simp] lemma return_seq_eq_map (f : α → β) : return f <*> oa = f <$> oa := rfl

lemma return_seq_dist_equiv_map (f : α → β ) : return f <*> oa ≃ₚ f <$> oa := dist_equiv.rfl

protected lemma seq_eq_bind_map : (og <*> oa) = (og >>= λ g, g <$> oa) := rfl

lemma seq_dist_equiv_bind_map : (og <*> oa) ≃ₚ (og >>= λ g, g <$> oa) := dist_equiv.rfl

@[simp] lemma support_seq : (og <*> oa).support = ⋃ g ∈ og.support, g '' oa.support :=
by simp only [oracle_comp.seq_eq_bind_map, support_bind, support_map]

@[simp] lemma fin_support_seq [decidable_eq α] [decidable_eq (α → β)] [decidable_eq β] :
  (og <*> oa).fin_support = og.fin_support.bUnion (λ g, oa.fin_support.image g) :=
by simp [fin_support_eq_iff_support_eq_coe, mem_fin_support_iff_mem_support]

lemma eval_dist_seq : ⁅og <*> oa⁆ = ⁅og⁆.bind (λ g, ⁅oa⁆.map g) :=
by simp [oracle_comp.seq_eq_bind_map]

@[simp] lemma eval_dist_seq' : ⁅og <*> oa⁆ = ⁅og⁆.seq ⁅oa⁆ := eval_dist_seq og oa

@[simp] lemma prob_output_seq_eq_tsum [decidable_eq β] (y : β) :
  ⁅= y | og <*> oa⁆ = ∑' (g : α → β) x, if y = g x then ⁅= g | og⁆ * ⁅= x | oa⁆ else 0 :=
by simp only [oracle_comp.seq_eq_bind_map, prob_output_bind_eq_tsum, prob_output_map_eq_tsum,
  ← ennreal.tsum_mul_left, eval_dist_apply_eq_prob_output, mul_ite, mul_zero]

lemma prob_output_seq_eq_tsum_indicator (y : β) :
  ⁅= y | og <*> oa⁆ = ∑' (g : α → β) x, ⁅= g | og⁆ * (g ⁻¹' {y}).indicator ⁅oa⁆ x :=
by simp only [oracle_comp.seq_eq_bind_map, prob_output_bind_eq_tsum, ← ennreal.tsum_mul_left,
  prob_output_map_eq_tsum_indicator]

@[simp] lemma prob_event_seq (e : set β) : ⁅e | og <*> oa⁆ = ∑' g, ⁅= g | og⁆ * ⁅g ⁻¹' e | oa⁆ :=
by simp [oracle_comp.seq_eq_bind_map, prob_event_bind_eq_tsum]

lemma prob_event_seq' (p : β → Prop) : ⁅p | og <*> oa⁆ = ∑' g, ⁅= g | og⁆ * ⁅p ∘ g | oa⁆ :=
prob_event_seq og oa p

@[simp] lemma prob_event_seq_eq_tsum_ite (e : set β) [decidable_pred (∈ e)] :
  ⁅e | og <*> oa⁆ = ∑' (g : α → β) x, if g x ∈ e then ⁅= g | og⁆ * ⁅= x | oa⁆ else 0 :=
by simp only [oracle_comp.seq_eq_bind_map, prob_event_bind_eq_tsum, prob_event_map_eq_tsum,
  ← ennreal.tsum_mul_left, eval_dist_apply_eq_prob_output, mul_ite, mul_zero]

lemma prob_event_seq_eq_tsum_ite' (p : set β) [decidable_pred p] :
  ⁅p | og <*> oa⁆ = ∑' (g : α → β) x, if g x ∈ p then ⁅= g | og⁆ * ⁅= x | oa⁆ else 0 :=
prob_event_seq_eq_tsum_ite og oa p

end seq

section seq_map

variables (oa oa' : oracle_comp spec α) (ob ob' : oracle_comp spec β)

lemma seq_map_eq_bind_bind (f : α → β → γ) :
  f <$> oa <*> ob = do {x ← oa, y ← ob, return (f x y)} :=
by simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, pure_bind]

@[simp] lemma support_seq_map (f : α → β → γ) : (f <$> oa <*> ob).support =
  {z | ∃ x ∈ oa.support, ∃ y ∈ ob.support, f x y = z} :=
by simp only [set.ext_iff, support_seq, support_map, set.mem_image, set.Union_exists,
  set.bUnion_and', set.Union_Union_eq_right, exists_prop, set.mem_Union, set.mem_set_of_eq,
  iff_self, implies_true_iff]

section comm

@[pairwise_dist_equiv] lemma seq_map_dist_equiv_comm_swap (f : α → β → γ) :
  f <$> oa <*> ob ≃ₚ f.swap <$> ob <*> oa :=
by simp only [seq_map_eq_bind_bind, bind_bind_dist_equiv_comm]

lemma seq_map_dist_equiv_comm (f : α → α → β) (hf : ∀ x x', f x x' = f x' x) :
  f <$> oa <*> oa' ≃ₚ f <$> oa' <*> oa :=
begin
  rw_dist_equiv [seq_map_dist_equiv_comm_swap],
  have : f.swap = f := by simp only [function.funext_iff, function.swap, hf, eq_self_iff_true],
  rw [this],
end

end comm

lemma prob_event_seq_map_eq_prob_event_preimage_uncurry (f : α → β → γ) (e : set γ) :
  ⁅e | f <$> oa <*> ob⁆ = ⁅(function.uncurry f) ⁻¹' e | prod.mk <$> oa <*> ob⁆ :=
by simpa only [← prob_event_map _ (function.uncurry f), map_seq, map_map_eq_map_comp]

lemma prob_event_seq_map_eq_prob_event_comp_uncurry (f : α → β → γ) (p : γ → Prop) :
  ⁅p | f <$> oa <*> ob⁆ = ⁅p ∘ function.uncurry f | prod.mk <$> oa <*> ob⁆ :=
by simpa only [← prob_event_map' _ (function.uncurry f), map_seq, map_map_eq_map_comp]

lemma prob_output_seq_map_prod_mk {f : α → β → γ} {z : γ} (x : α) (y : β)
  (h : f x y = z) (h' : ∀ x' ∈ oa.support, ∀ y' ∈ ob.support, f x' y' = z → x' = x ∧ y' = y):
  ⁅= z | f <$> oa <*> ob⁆ = ⁅= x | oa⁆ * ⁅= y | ob⁆ :=
begin
  rw [seq_map_eq_bind_bind],
  refine trans (prob_output_bind_eq_single' _ _ z x _) _,
  { simp only [support_bind_return, set.mem_image, forall_exists_index, and_imp],
    exact λ x' hx' y' hy' hxy', (h' x' hx' y' hy' hxy').1 },
  { by_cases hx : x ∈ oa.support,
    { refine congr_arg (λ r, _ * r) (prob_output_bind_return_eq_single' _ _ _ y h _),
      exact λ y' hy' hxy', (h' x hx y' hy' hxy').2, },
    { simp_rw [prob_output_eq_zero hx, zero_mul] } } 
end

lemma prob_event_seq_map_prod_mk (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (e : set (α × β)) :
  ⁅e | prod.mk <$> oa <*> ob⁆ =
    ∑' z, e.indicator (λ z, ⁅= z.1 | oa⁆ * ⁅= z.2 | ob⁆) z :=
begin
  rw [prob_event_eq_tsum_indicator],
  refine tsum_congr (λ z, _),
  by_cases hz : z ∈ e,
  { simp only [set.indicator_of_mem hz],
    exact prob_output_seq_map_prod_mk oa ob z.1 z.2 prod.mk.eta
      (λ x hx y hy h, prod.eq_iff_fst_eq_snd_eq.1 h) },
  { simp only [set.indicator_of_not_mem hz] }
end

/-- If the results of the computations `oa` and `ob` are combined with some function `f`,
and `e` is an event such that outputs of `f` are in `e` iff the individual components
lie in some other events `e1` and `e2`, then the probability of the event `e` is the
product of the probabilites holding individually.
For example this applies if `f` is `::`, `e` is defined elementwise,
and `e1` and `e2` are the portions of `e` for the head and tail respectively. -/
lemma prob_event_seq_map_eq_mul (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (f : α → β → γ) (e : set γ) (e1 : set α) (e2 : set β)
  (h : ∀ x ∈ oa.support, ∀ y ∈ ob.support, f x y ∈ e ↔ x ∈ e1 ∧ y ∈ e2) :
  ⁅e | f <$> oa <*> ob⁆ = ⁅e1 | oa⁆ * ⁅e2 | ob⁆ :=
begin
  rw [prob_event_seq_map_eq_prob_event_preimage_uncurry, prob_event_seq_map_prod_mk],
  simp_rw [prob_event_eq_tsum_indicator, ← ennreal.tsum_mul_right, ← ennreal.tsum_mul_left,
    ← ennreal.tsum_prod],
  refine tsum_congr (λ z, _),
  cases z with x y,
  by_cases hxy : x ∈ oa.support ∧ y ∈ ob.support,
  { specialize h x hxy.1 y hxy.2,
    by_cases hpf : x ∈ e1 ∧ y ∈ e2,
    { simp only [set.indicator_of_mem hpf.1, set.indicator_of_mem hpf.2,
        set.indicator_apply_eq_self, set.mem_preimage, function.uncurry_apply_pair, h, hpf,
        eval_dist_apply_eq_prob_output, true_and, not_true, is_empty.forall_iff] },
    { refine or.elim (not_and_distrib.1 hpf) (λ hp, _) (λ hp, _);
      simp only [set.indicator_of_not_mem hp, zero_mul, mul_zero, set.indicator_apply_eq_zero,
        set.mem_preimage, function.uncurry_apply_pair, h, hpf, is_empty.forall_iff] } },
  { simp_rw [not_and_distrib, ← prob_output_eq_zero_iff] at hxy,
    cases hxy with hx hy,
    { have : e1.indicator ⁅oa⁆ x = 0 := set.indicator_apply_eq_zero.2 (λ hx', hx),
      simp only [this, hx, zero_mul, set.indicator_apply_eq_zero,
        eq_self_iff_true, implies_true_iff]},
    { have : e2.indicator ⁅ob⁆ y = 0 := set.indicator_apply_eq_zero.2 (λ hy', hy),
      simp only [this, hy, mul_zero, set.indicator_apply_eq_zero,
        eq_self_iff_true, implies_true_iff] } }
end

end seq_map

end oracle_comp