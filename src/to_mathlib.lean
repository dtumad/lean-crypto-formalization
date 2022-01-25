import measure_theory.probability_mass_function.basic
-- import analysis.special_functions.exp_log
import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials 

import data.vector.basic
import data.vector.zip

/-!
# Miscelanious Lemams

This file is a collection of random statements that maybe should eventually move to mathlib.
Most of these are things that could usually be "handwaved" away in proofs. 
-/

@[simp] 
theorem prod.forall₃ {α β γ : Type*}
  {p : α × β × γ → Prop} : (∀ x, p x) ↔ (∀ a b c, p (a, b, c)) :=
⟨assume h a b c, h (a, b, c), assume h ⟨a, b, c⟩, h a b c⟩

section asymptotics

open asymptotics

lemma inv_is_O_inv_iff {α 𝕜 𝕜' : Type*} [preorder α] [normed_field 𝕜] [normed_field 𝕜']
  {l : filter α} {f : α → 𝕜} {g : α → 𝕜'}
  (hf : ∀ᶠ x in l, ∥f x∥ ≠ 0) (hg : ∀ᶠ x in l, ∥g x∥ ≠ 0) :
  is_O (λ n, (f n)⁻¹) (λ n, (g n)⁻¹) l ↔ is_O g f l :=
begin
  let hfg := filter.eventually.and hf hg,
  have hfg : ∀ᶠ x in l, 0 < ∥f x∥ ∧ 0 < ∥g x∥ := begin
    refine filter.sets_of_superset _ hfg (λ x hx, by simpa using hx),
  end,
  simp only [is_O_iff],
  refine exists_congr (λ c, ⟨λ hc, _, λ hc, _⟩),
  {

    refine filter.sets_of_superset _ (hc.and hfg) _,
    intros x hx,
    obtain ⟨hx, hx0⟩ := hx,
    simp_rw [ normed_field.norm_inv, inv_eq_one_div, ← mul_div_assoc,
      mul_one, div_le_iff hx0.1, div_mul_eq_mul_div] at hx,
    refine (one_le_div hx0.2).1 hx,
  },
  {
    refine filter.sets_of_superset _ (hc.and hfg) _,
    intros x hx,
    simp_rw [set.mem_set_of_eq, normed_field.norm_inv, inv_eq_one_div, ← mul_div_assoc,
      mul_one, div_le_iff hx.2.1, div_mul_eq_mul_div],
    refine (one_le_div hx.2.2).2 hx.1,
  },
end

end asymptotics

section const_pmf

lemma sum_inv_fintype_card_eq_one {A : Type*} [fintype A] [inhabited A] :
  has_sum (λ (a : A), (fintype.card A : nnreal)⁻¹) 1 :=
begin
  convert has_sum_fintype (λ (a : A), (fintype.card A : nnreal)⁻¹),
  rw [finset.sum_const, nsmul_eq_mul],
  refine (div_self _).symm,
  exact nat.cast_ne_zero.2 (finset.card_ne_zero_of_mem (by simp : arbitrary A ∈ _)),
end

/-- Definition of a uniform `pmf` on a finite type -/
noncomputable def pmf.const (α : Type*) [fintype α] [inhabited α] : pmf α :=
⟨λ a, (fintype.card α : nnreal)⁻¹, sum_inv_fintype_card_eq_one⟩

@[simp] lemma pmf.const_apply {α : Type*} [fintype α] [inhabited α]
  (a : α) : pmf.const α a = (fintype.card α : nnreal)⁻¹ := rfl

lemma card_ne_zero_of_inhabited {α : Type*} [fintype α] [inhabited α] : 
  fintype.card α ≠ 0 :=
finset.card_ne_zero_of_mem (finset.mem_univ (arbitrary α))

end const_pmf

section misc

lemma ite_le {A : Type*} [has_le A] {a b c : A} (p : Prop) [decidable p]
  (hab : b ≤ a) (hac : c ≤ a) : ite p b c ≤ a :=
by split_ifs; assumption

section sum_stuff

lemma list.sum_eq_zero_of_mem_zero {G : Type} [add_monoid G] :
  ∀ (gs : list G) (h : ∀ g ∈ gs, g = (0 : G)), gs.sum = 0
| [] _ := list.sum_nil
| (g :: gs) h := begin
  rw [list.sum_cons, h g (list.mem_cons_self g gs), zero_add],
  exact list.sum_eq_zero_of_mem_zero gs (λ g' hg', h g' $ list.mem_cons_of_mem g hg'),
end

lemma list.sum_eq_of_unique {G : Type} [add_comm_group G] :
  ∀ (gs : list G) (g : G)
    (n : ℕ) (hn : gs.nth n = some g)
    (hng : ∀ (m : ℕ) (hm : m < gs.length), m ≠ n → gs.nth_le m hm = 0),
    gs.sum = g
| [] g n hn hng := by contradiction
| (g' :: gs) g 0 hn hng := begin
  have hg' : g' = g := by simpa using hn,
  have hgs : gs.sum = 0 := begin
    refine list.sum_eq_zero_of_mem_zero gs (λ x hx, _),
    obtain ⟨m, hm, rfl⟩ := list.mem_iff_nth_le.mp hx,
    exact hng m.succ (by simpa using nat.succ_lt_succ hm) (nat.succ_ne_zero m),
  end,
  simp [hg', hgs],
end
| (g' :: gs) g (n + 1) hn hng := begin
  have hg' : g' = 0,
  from hng 0 (nat.zero_lt_succ _) (by contradiction),
  have hgs : gs.sum = g := begin
    apply list.sum_eq_of_unique gs g n hn,
    intros m hm hmn,
    refine hng (m + 1) (nat.succ_lt_succ hm) (nat.succ_ne_succ.2 hmn),
  end,
  simp [hg', hgs],
end

end sum_stuff

@[simp]
lemma vector.cons_eq_cons_iff {A : Type*} {n : ℕ} 
  (a a' : A) (v v' : vector A n) :
  a ::ᵥ v = a' ::ᵥ v' ↔ a = a' ∧ v = v' :=
⟨λ h, ⟨by simpa using congr_arg vector.head h, by simpa using congr_arg vector.tail h⟩,
  λ h, by rw [h.1, h.2]⟩

@[simp]
lemma vector_to_list_nth_le'' {A : Type} {n : ℕ} (v : vector A n)
  (m : ℕ) (hm : m < v.to_list.length) :
  v.to_list.nth_le m hm = v.nth ⟨m, lt_of_lt_of_le hm (le_of_eq (vector.to_list_length _))⟩ :=
begin
  induction v,
  simpa,
end

@[simp]
lemma vector.to_list_nth {A : Type} {n : ℕ} (v : vector A n)
  (i : fin n) : v.to_list.nth i = some (v.nth i) :=
begin
  induction v,
  simp,
  rw list.nth_eq_some,
  refine ⟨lt_of_lt_of_le i.2 (le_of_eq v_property.symm), rfl⟩,
end

@[simp]
lemma list.append_eq_append_iff_left {A : Type} (x y z : list A) :
  x ++ y = x ++ z ↔ y = z :=
begin
  induction x with x xs h,
  { simp },
  { simp [h] }
end

-- @[simp]
-- lemma list.append_eq_append_iff_right {A : Type} :
--   ∀ (x y z : list A), x ++ z = y ++ z ↔ x = y
-- | [] [] z := by simp
-- | [] ys [] := by simp
-- | [] ys (z :: zs) := begin
--   simp,
--   refine (list.cons_eq_append_iff).trans _,
--   simp,
-- end
-- | (x :: xs) [] z := sorry
-- | (x :: xs) (y :: ys) z := sorry

@[simp]
lemma list.of_fn_eq_vector_to_list_iff {A : Type} {n : ℕ}
  (f : fin n → A) (v : vector A n) :
  list.of_fn f = v.to_list ↔
    vector.of_fn f = v :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    ext j,
    rw [vector.nth_of_fn],
    have hj1 : j.1 < (list.of_fn f).length := (list.length_of_fn f).symm ▸ j.2,
    suffices : (list.of_fn f).nth_le j hj1 = v.to_list.nth_le j ((vector.to_list_length v).symm ▸ j.2),
    by simpa using this,
    congr,
    exact h,
  },
  {
    ext n a,
    rw ← h,
    simp,
  },
end

-- TODO: See if this is the best approach for this.
instance list.subset_decidable {A : Type} 
  [decidable_eq A] : ∀ (as as' : list A), decidable (as ⊆ as')
| [] as' := is_true (list.nil_subset as')
| (a :: as) as' := by simpa using @and.decidable _ _ _ (list.subset_decidable as as')

end misc