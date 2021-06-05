import crypto_foundations.comp
import measure_theory.probability_mass_function

/-!
# Distributional Semantics of comp Evaluation

This file defines the probability distribution of evaluation a `comp A`.
The distribution is given by a probability mass function `pmf A` on the underlying type.
This requires providing a proof of well formedness to ensure the distribution sums to `1`.

From this we can define `comp.Pr_prop p`, where `p : A → Prop`,
to be the probability that `p` holds on the result of the nondeterministic computation.
-/

open_locale big_operators nnreal

noncomputable theory

namespace comp

variables {A B : Type}

section eval_distribution

/-- Used to bootstrap `eval_distribution` and `eval_distribution_ne_zero_iff` -/
private def eval_distribution' (ca : comp A) : 
  ca.is_well_formed → Σ (da : pmf A), plift (∀ (a : A), (da a ≠ 0 ↔ a ∈ ca.support)) :=
begin
  refine ca.rec_on _ _ _ _,
  { exact λ _ _ a _, ⟨pmf.pure a, plift.up (by simp)⟩ },
  { refine λ A B ca cb db da h, _,
    rw is_well_formed_bind_iff at h,
    refine ⟨(db h.1).1.bind_on_support (λ b hb, (da b (h.2 b ((plift.down (db h.1).2 b).mp hb))).1), 
      plift.up (λ a, _)⟩,
    rw [mem_support_bind_iff, pmf.bind_on_support_apply,
      tsum_ne_zero_iff (pmf.bind_on_support.summable (db _).1 _ _)],
    split; rintro ⟨b, hb⟩; refine ⟨b, _⟩,
    { simp only [not_or_distrib, ne.def, mul_eq_zero] at hb,
      simp only [dif_neg hb.left] at hb,
      rwa [← plift.down (db h.1).2, ← plift.down (da b (h.2 b ((plift.down (db h.1).2 b).mp hb.1) )).2] },
    { have : (db h.1).1 b ≠ 0 := (plift.down (db h.1).2 _).mpr hb.1,
      simp only [not_or_distrib, ne.def, mul_eq_zero, dif_neg this],
      have := hb.1,
      rwa [← plift.down (db h.1).2, ← plift.down (da b (h.2 b this)).2] at hb } },
  { introsI A _ _ _ _,
    refine ⟨pmf.const A, plift.up (λ a, by simpa using card_ne_zero_of_inhabited)⟩ },
  { introsI A p hp ca da h,
    rw is_well_formed_repeat_iff at h,
    have : ∃ a (ha : p a), (da h.1).1 a ≠ 0,
    { refine h.2.rec (λ a ha, _),
      rw mem_support_repeat at ha,
      refine ⟨a, ha.2, (plift.down (da h.1).2 _).2 ha.1⟩ },
    refine ⟨(da h.1).1.filter p this, 
      plift.up (λ a, by rw [mem_support_repeat ca p a, pmf.filter_apply_ne_zero_iff, 
        ← (plift.down (da h.1).2 _), set.mem_inter_iff, pmf.mem_support_iff, set.mem_def])⟩ }
end

/-- The denotational semantics of a `comp A` is the distribution of resulting values.
  This distribution is given in the form of a `pmf` on the type `A` of the computation.
  Defined for any computation with nonempty support, but only meaningful if `ca` is well formed -/
def eval_distribution (ca : comp A) [ca.is_well_formed] : pmf A :=
(eval_distribution' ca (by apply_instance)).fst

theorem eval_distribution_ne_zero_iff (ca : comp A) [ca.is_well_formed] (a : A) :
  eval_distribution ca a ≠ 0 ↔ a ∈ ca.support :=
(plift.down (eval_distribution' ca (by apply_instance)).snd) a

lemma zero_lt_eval_distribution_iff (ca : comp A) [ca.is_well_formed] (a : A) :
  0 < eval_distribution ca a ↔ a ∈ ca.support :=
iff.trans ⟨λ h, ne_of_gt h, λ h, lt_of_le_of_ne zero_le' h.symm⟩ (eval_distribution_ne_zero_iff ca a)

lemma eval_distribution_eq_zero_of_not_mem_support {ca : comp A} [ca.is_well_formed] {a : A}
  (ha : a ∉ ca.support) : ca.eval_distribution a = 0 :=
not_not.1 $ (mt (eval_distribution_ne_zero_iff ca a).1) ha

lemma eval_distribution_support_eq_support (ca : comp A) [ca.is_well_formed] :
  (eval_distribution ca).support = ca.support :=
set.ext (λ a, eval_distribution_ne_zero_iff ca a)

@[simp] lemma eval_distribution_ret [decidable_eq A] (a : A) :
  eval_distribution (ret a) = pmf.pure a := 
rfl

-- /-- If `ca b` is not well formed for all `b ∉ ca.support`, then we can reduce to `bind'`-/
-- @[simp]
-- lemma eval_distribution_bind' (cb : comp B) (ca : B → comp A)
--   [cb.is_well_formed] (hca : ∀ b ∈ cb.support, (ca b).is_well_formed) :
--   eval_distribution (bind cb ca) = (eval_distribution cb).bind_on_support
--     (λ b hb, (eval_distribution (ca b))) := rfl

/-- If we generalize `ha` over all `b` we can further reduce the `bind'` above to `bind`-/
@[simp]
lemma eval_distribution_bind (cb : comp B) (ca : B → comp A) [cb.is_well_formed] [∀ b, (ca b).is_well_formed] : 
  eval_distribution (bind cb ca) = (eval_distribution cb).bind (λ b, eval_distribution (ca b)) :=
trans (by reflexivity) (pmf.bind_on_support_eq_bind (eval_distribution cb) _)

@[simp] lemma eval_distribution_rnd {A : Type} [inhabited A] [fintype A] [decidable_eq A] 
  : eval_distribution (rnd A) = pmf.const A := 
rfl

end eval_distribution

section probabilities

/-- Probability of a property holding after evaluating the computation -/
def Pr_prop {A : Type} (ca : comp A) [ca.is_well_formed]
  (p : A → Prop) [decidable_pred p] : ℝ≥0 :=
∑' (a : A), if p a then ca.eval_distribution a else 0

notation ca `-Pr[` p `]` := ca.Pr_prop p

variables (ca : comp A) 
variable [ca.is_well_formed]

lemma Pr_prop_le_one (p : A → Prop) [decidable_pred p] : 
  ca-Pr[p] ≤ 1 :=
have ∀ a, ite (p a) (ca.eval_distribution a) 0 ≤ ca.eval_distribution a,
from λ a, ite_le (p a) le_rfl zero_le',
(ca.eval_distribution).tsum_coe ▸ (tsum_le_tsum this 
    (nnreal.summable_of_le this (ca.eval_distribution).summable_coe) ((ca.eval_distribution).summable_coe))

theorem Pr_prop_of_unique [decidable_eq A] (p : A → Prop) [decidable_pred p]
  (a : A) (ha : p a) (hp : ∀ a', p a' → a' = a) : 
  ca-Pr[p] = ca.eval_distribution a :=
begin
  have := tsum_ite_eq a (ca.eval_distribution a),
  refine trans (tsum_congr (λ a', _)) this,
  split_ifs with hpa' h,
  { rw h },
  { exact absurd (hp a' hpa') h },
  { exact absurd (h.symm ▸ ha : p a') hpa' },
  { refl }
end

theorem Pr_prop_eq_one_iff (p : A → Prop) [decidable_pred p] :
  ca-Pr[p] = 1 ↔ ∀ a ∈ ca.support, p a :=
begin
  refine ⟨λ h a ha, _, λ h, _⟩,
  { rw ← zero_lt_eval_distribution_iff ca a at ha,
    by_contradiction hpa,
    suffices : ca.Pr_prop p < 1,
    from ne_of_lt this h,
    refine lt_of_lt_of_le _ (le_of_eq ca.eval_distribution.tsum_coe),
    have : ite (p a) (ca.eval_distribution a) 0 < ca.eval_distribution a,
    by simpa only [hpa, if_false] using ha,
    refine nnreal.tsum_lt_tsum (λ a, ite_le (p a) le_rfl zero_le') this ca.eval_distribution.summable_coe },
  { refine trans _ ca.eval_distribution.tsum_coe,
    unfold Pr_prop,
    refine congr_arg tsum (funext (λ a, _)),
    by_cases ha : a ∈ ca.support,
    { simp [h a ha] },
    { simp [eval_distribution_eq_zero_of_not_mem_support ha] } }
end

lemma Pr_prop_eq [decidable_eq A] (a : A) :
  ca-Pr[λ x, x = a] = ca.eval_distribution a :=
Pr_prop_of_unique ca (λ x, x = a) a rfl (λ _, id)

/-- Probability of a `comp bool` returning true -/
def Pr (ca : comp bool) [ca.is_well_formed] : ℝ≥0 := 
ca-Pr[λ x, x = tt]

lemma Pr_eq_eval_distribution_tt (ca : comp bool) [ca.is_well_formed] :
  ca.Pr = ca.eval_distribution tt :=
Pr_prop_eq ca tt

end probabilities

end comp