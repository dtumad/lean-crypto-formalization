import computational_monads.comp 
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

private noncomputable def eval_distribution' : Π {A : Type} (ca : comp A) [ca.is_well_formed], 
  Σ (da : pmf A), plift (∀ (a : A), (a ∈ da.support ↔ a ∈ ca.support))
| A (ret a) _ := ⟨pmf.pure a, plift.up (by simp)⟩
| A (@bind _ B ca cb) h := begin
  haveI : ca.is_well_formed := h.1,
  refine ⟨_, plift.up (λ a, _)⟩,
  { refine (pmf.bind_on_support (eval_distribution' ca).1 (λ a ha, _)),
    haveI : (cb a).is_well_formed := h.2 a (((plift.down (eval_distribution' ca).2) a).mp ha),
    refine (eval_distribution' (cb a)).1 },
  { rw [pmf.mem_support_iff, mem_support_bind_iff, pmf.bind_on_support_apply,
      tsum_ne_zero_iff (pmf.bind_on_support.summable (eval_distribution' ca).1 _ _)],
    split; rintro ⟨b, hb⟩; refine ⟨b, _⟩,
    { simp only [not_or_distrib, ne.def, mul_eq_zero] at hb,
      simp only [dif_neg hb.left] at hb,
      haveI : (cb b).is_well_formed := (h.2 b ((plift.down (eval_distribution' ca).2 b).mp hb.1)),
      rw [← plift.down (eval_distribution' ca).2, ← plift.down (eval_distribution' (cb b)).2],
      exact ⟨hb.1, hb.2⟩ },
    { rw exists_prop at hb,
      simp only [not_or_distrib, ne.def, mul_eq_zero],
      rw dif_neg _,
      { haveI : (cb b).is_well_formed := h.2 b hb.1,
        rwa [← plift.down (eval_distribution' ca).2, 
          ← plift.down (eval_distribution' (cb b)).2,
          pmf.mem_support_iff, pmf.mem_support_iff] at hb },
      { exact ((plift.down (eval_distribution' ca).2) _).2 hb.1 } } }
end
| A (@rnd _ fA iA) _ := begin
  haveI := fA, haveI := iA,
  exact ⟨@pmf.const A fA iA, plift.up (by simpa using card_ne_zero_of_inhabited)⟩
end
| A (@repeat _ p hp ca) h := begin
  haveI : ca.is_well_formed := h.1,
  have : ∃ a (ha : p a), (eval_distribution' ca).1 a ≠ 0,
  { refine h.2.rec (λ a ha, _),
    exact ⟨a, ha.2, (plift.down (eval_distribution' ca).2 _).2 ha.1⟩ },
  exact ⟨(eval_distribution' ca).1.filter p this, plift.up (λ a, 
    by rw [pmf.mem_support_iff, mem_support_repeat_iff ca p a, pmf.filter_apply_ne_zero_iff, 
      ← (plift.down (eval_distribution' ca).2 _), set.mem_inter_iff, 
      pmf.mem_support_iff, set.mem_def])⟩
end

/-- The denotational semantics of a `comp A` is the distribution of resulting values.
  This distribution is given in the form of a `pmf` on the type `A` of the computation.
  Defined for any computation with nonempty support, but only meaningful if `ca` is well formed -/
def eval_distribution (ca : comp A) [ca.is_well_formed] : pmf A :=
(eval_distribution' ca).fst

@[simp]
theorem mem_support_eval_distribution_iff (ca : comp A) [ca.is_well_formed] (a : A) :
  a ∈ (eval_distribution ca).support ↔ a ∈ ca.support :=
(plift.down (eval_distribution' ca).snd) a

lemma mem_support_of_mem_support_eval_distribution {ca : comp A} [ca.is_well_formed] {a : A}
  (h : a ∈ (eval_distribution ca).support) : a ∈ ca.support :=
(mem_support_eval_distribution_iff ca a).mp h

lemma mem_support_eval_distribution_of_mem_support {ca : comp A} [ca.is_well_formed] {a : A}
  (h : a ∈ ca.support) : a ∈ (eval_distribution ca).support :=
(mem_support_eval_distribution_iff ca a).mpr h

@[simp]
theorem eval_distribution_ne_zero_iff (ca : comp A) [ca.is_well_formed] (a : A) :
  eval_distribution ca a ≠ 0 ↔ a ∈ ca.support :=
mem_support_eval_distribution_iff ca a

@[simp]
lemma zero_lt_eval_distribution_iff (ca : comp A) [ca.is_well_formed] (a : A) :
  0 < eval_distribution ca a ↔ a ∈ ca.support :=
iff.trans ⟨λ h, ne_of_gt h, λ h, lt_of_le_of_ne zero_le' h.symm⟩ (eval_distribution_ne_zero_iff ca a)

lemma eval_distribution_eq_zero_of_not_mem_support {ca : comp A} [ca.is_well_formed] {a : A}
  (ha : a ∉ ca.support) : ca.eval_distribution a = 0 :=
not_not.1 $ (mt (eval_distribution_ne_zero_iff ca a).1) ha

@[simp]
lemma eval_distribution_support_eq_support (ca : comp A) [ca.is_well_formed] :
  (eval_distribution ca).support = ca.support :=
set.ext (λ a, eval_distribution_ne_zero_iff ca a)

@[simp] 
lemma eval_distribution_ret (a : A) :
  eval_distribution (ret a) = pmf.pure a := 
rfl

@[simp]
lemma eval_distribution_bind' (cb : comp B) (ca : B → comp A)
  [h : (cb.bind ca).is_well_formed] :
  -- [cb.is_well_formed] [hca : ∀ b ∈ cb.support, (ca b).is_well_formed] :
  eval_distribution (bind cb ca) = 
    (@eval_distribution B cb (is_well_formed_of_bind_left h)).bind_on_support (λ b hb, 
      (@eval_distribution A (ca b) (
        is_well_formed_of_bind_right h b
          (@mem_support_of_mem_support_eval_distribution B cb (is_well_formed_of_bind_left h) _ hb)
      ))) :=
begin
  rw [eval_distribution, eval_distribution'],
  refl,
end

/-- If `ca b` is not well formed for all `b ∉ ca.support`, then we can reduce to `bind` instead of `bind_on_support`-/
@[simp]
lemma eval_distribution_bind (cb : comp B) (ca : B → comp A)
  [cb.is_well_formed] [∀ b, (ca b).is_well_formed] :
  (bind cb ca).eval_distribution =
    (cb.eval_distribution).bind (λ b, (ca b).eval_distribution) :=
trans (eval_distribution_bind' cb ca)
begin
  convert (pmf.bind_on_support_eq_bind cb.eval_distribution _),
  refl,
end

@[simp] 
lemma eval_distribution_rnd {A : Type} [inhabited A] [fintype A] :
  eval_distribution (rnd A) = pmf.const A := 
rfl

@[simp]
lemma eval_distribution_bind_ret (a : A) (cb : A → comp B)
  [∀ a, (cb a).is_well_formed] :
  ((comp.ret a).bind cb).eval_distribution =
    (cb a).eval_distribution :=
by simp

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

@[simp]
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

@[simp]
-- TODO: maybe just get rid of this definition?
lemma Pr_def (ca : comp bool) [ca.is_well_formed] :
  Pr ca = (ca-Pr[λ x, x = tt]) :=
rfl

lemma Pr_eq_eval_distribution_tt (ca : comp bool) [ca.is_well_formed] :
  ca.Pr = ca.eval_distribution tt :=
Pr_prop_eq ca tt

end probabilities

end comp