import data.bitvec.basic
import measure_theory.probability_mass_function
import algebra.big_operators

open_locale big_operators nnreal

/-- Collection of random statements that should eventually port to mathlib -/

variables {A B : Type*}

@[simp] lemma finset.bUnion_nonempty_iff [decidable_eq B] (s : finset A) (t : A → finset B) :
  (finset.bUnion s t).nonempty ↔ ∃ a, a ∈ s ∧ (t a).nonempty :=
⟨λ h, let ⟨b, hb⟩ := h in let ⟨a, ha, hab⟩ := finset.mem_bUnion.mp hb in ⟨a, ha, b, hab⟩, 
  λ h, let ⟨a, ha, ⟨b, hb⟩⟩ := h in ⟨b, finset.mem_bUnion.mpr ⟨a, ha, hb⟩⟩⟩

lemma pmf.bind'.summable (p : pmf A) (f : ∀ a ∈ p.support, pmf B) (b : B) :
  summable (λ a : A, p a * dite (p a = 0) (λ _, (0 : nnreal)) (λ h, f a h b)) :=
begin
  refine nnreal.summable_of_le (assume a, _) p.summable_coe,
  split_ifs,
  { refine (mul_zero (p a)).symm ▸ le_of_eq h.symm },
  { suffices : p a * f a h b ≤ p a * 1, { simpa },
    exact mul_le_mul_of_nonneg_left ((f a h).coe_le_one _) (p a).2 }
end

@[simp] lemma pmf.support_pure (a : A) : (pmf.pure a).support = {a} :=
le_antisymm (λ a ha, by simpa using ha) (λ a ha, by simpa using ha)

noncomputable def pmf.bind' (p : pmf A) (f : ∀ a ∈ p.support, pmf B) : pmf B :=
⟨λ b, ∑' a, p a * dite (p a = 0) (λ _, 0) (λ h, f a h b), 
begin
  apply ennreal.has_sum_coe.1,
  simp only [ennreal.coe_tsum (pmf.bind'.summable p f _)],
  rw [ennreal.summable.has_sum_iff, ennreal.tsum_comm],
  simp only [ennreal.coe_mul, ennreal.coe_one, ennreal.tsum_mul_left],
  have : ∑' (a : A), (p a : ennreal) = 1 := by simp [← ennreal.coe_tsum p.summable_coe],
  convert this,
  refine funext (λ a, _),
  split_ifs with h,
  { simp [h] },
  { simp [← ennreal.coe_tsum (f a h).summable_coe, (f a h).tsum_coe] }
end⟩

lemma pmf.bind'_apply (p : pmf A) (f : ∀ a ∈ p.support, pmf B) (b : B) :
  p.bind' f b = ∑' a, p a * dite (p a = 0) (λ _, 0) (λ h, f a h b) := rfl

lemma pmf.bind'_eq_bind (p : pmf A) (f : A → pmf B) :
  p.bind' (λ a _, f a) = p.bind f :=
begin
  ext b,
  simp [p.bind'_apply (λ a _, f a)],
  refine congr_arg _ (funext (λ a, _)),
  split_ifs,
  { simp [h] },
  { exact rfl },
end

@[simp] lemma card_bitvec {n : ℕ} : fintype.card (bitvec n) = 2 ^ n :=
by rw [card_vector n, fintype.card_bool]

lemma sum_inv_fintype_card_eq_one {A : Type*} [fintype A] [inhabited A] :
  has_sum (λ (a : A), (fintype.card A : nnreal)⁻¹) 1 :=
begin
  convert has_sum_fintype (λ (a : A), (fintype.card A : nnreal)⁻¹),
  rw [finset.sum_const, nsmul_eq_mul],
  refine (div_self _).symm,
  rw [ne.def, nat.cast_eq_zero],
  exact finset.card_ne_zero_of_mem (by simp : arbitrary A ∈ _),
end

noncomputable def pmf.const (α : Type*) [fintype α] [inhabited α] : pmf α :=
⟨λ a, (fintype.card α : nnreal)⁻¹, sum_inv_fintype_card_eq_one⟩

@[simp] lemma pmf.const_apply {α : Type*} [fintype α] [inhabited α]
  (a : α) : pmf.const α a = (fintype.card α : nnreal)⁻¹ := rfl

lemma tsum_ne_zero_iff {α : Type*} (f : α → ℝ≥0) (hf : summable f) :
  tsum f ≠ 0 ↔ ∃ (a : α), f a ≠ 0 :=
by rwa [ne.def, tsum_eq_zero_iff hf, not_forall]

def decidable_eq_of_prod_left {A B : Type*} [inhabited B] [h : decidable_eq (A × B)] : 
  decidable_eq A :=
λ a a', decidable.rec (λ h, is_false (λ h', h (prod.mk.inj_iff.mpr ⟨h', rfl⟩))) 
  (λ h, is_true (prod.mk.inj_iff.mp h).1) (h ⟨a, arbitrary B⟩ ⟨a', arbitrary B⟩)

lemma card_ne_zero_of_inhabited {α : Type*} [fintype α] [inhabited α] : 
  fintype.card α ≠ 0 :=
finset.card_ne_zero_of_mem (finset.mem_univ (arbitrary α))