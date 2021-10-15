import measure_theory.probability_mass_function
import analysis.special_functions.exp_log
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

lemma eventually_one_le_rat_norm : ∀ᶠ (x : ℕ) in filter.at_top, 1 ≤ ∥(x : ℚ)∥ :=
begin
  rw filter.eventually_at_top,
  refine ⟨1, λ x hx, le_abs.2 $ or.inl _⟩,
  simpa only [nat.one_le_cast, rat.cast_coe_nat],
end


lemma fpow_is_O_fpow_of_le {α 𝕜 : Type*} [preorder α] [normed_field 𝕜] 
  (f : α → 𝕜)
  {a b : ℤ} (h : a ≤ b) (h' : ∀ᶠ (x : α) in filter.at_top, 1 ≤ ∥f x∥):
  (is_O (λ n, (f n) ^ a) (λ n, (f n) ^ b) filter.at_top) :=
begin
  refine is_O.of_bound 1 _,
  refine filter.sets_of_superset filter.at_top h' _,
  intros x hx,
  simp only [one_mul, normed_field.norm_fpow, set.mem_set_of_eq],
  refine fpow_le_of_le hx h,
end

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

lemma nat_coe_tendsto (R : Type*) [linear_ordered_ring R] [archimedean R] : 
  filter.tendsto (λ (n : ℕ), (↑n : R)) filter.at_top filter.at_top :=
begin
  refine filter.tendsto_at_top.2 (λ x, _),
  obtain ⟨m, hm⟩ := exists_nat_ge x,
  rw filter.eventually_at_top,
  refine ⟨m, λ y hy, hm.trans $ nat.cast_le.2 hy⟩,
end

lemma nat_coe_eventually_ne_zero (R : Type*) [linear_ordered_ring R] [archimedean R] :
  ∀ᶠ (x : ℕ) in filter.at_top, (x : R) ≠ 0 :=
begin
  simp only [filter.eventually_at_top, ge_iff_le, ne.def, nat.cast_eq_zero],
  exact ⟨1, λ x hx h, not_le_of_lt zero_lt_one (le_trans hx (le_of_eq h))⟩,
end

-- This is the main lemma that doesn't generalize away from ℝ
lemma real.norm_nat_coe_eventually_ge (c : ℝ) :
  ∀ᶠ (x : ℕ) in filter.at_top, c ≤ ∥(x : ℝ)∥ :=
begin
  simp,
  obtain ⟨y, hy⟩ := exists_nat_ge c,
  refine ⟨y, λ x hx, hy.trans _⟩,
  simpa,
end

@[simp]
lemma comap_nat_coe_at_top (R : Type*) [linear_ordered_ring R] [archimedean R] : 
  filter.comap (λ n, ↑n : ℕ → R) filter.at_top = 
  (filter.at_top : filter ℕ) :=
begin
  ext t,
  split,
  {
    intro h,
    rw filter.mem_comap at h,
    -- rw filter.mem_comap_sets at h,
    obtain ⟨s, hs, h⟩ := h,
    rw filter.mem_at_top_sets at hs ⊢,
    obtain ⟨a, ha⟩ := hs,
    obtain ⟨b, hb⟩ := exists_nat_ge a,
    refine ⟨b, λ x hx, h _⟩,
    rw set.mem_preimage,
    refine ha x (hb.trans _),
    rw nat.cast_le,
    exact hx,
  },
  {
    intro h,
    rw filter.mem_comap,
    rw filter.mem_at_top_sets at h,
    obtain ⟨a, ha⟩ := h,
    refine ⟨set.Ici ↑a, _, _⟩,
    {
      simp,
      refine ⟨↑a, λ b, id⟩,
    },
    {
      intros x hx,
      rw [set.mem_preimage, set.mem_Ici, nat.cast_le] at hx,
      refine ha x hx,
    }
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

section log_exp

open real

lemma log_le_of_nonneg {x : ℝ} (hx : x ≥ 0) : log x ≤ x :=
begin
  cases lt_or_eq_of_le hx with hx' hx',
  { calc log x ≤ log (exp x) : (log_le_log hx' (exp_pos x)).mpr 
        (trans (by linarith) (add_one_le_exp_of_nonneg hx))
      ... = x : by simp },
  { simp [← hx'] }
end

lemma neg_log_le_of_nonneg {x : ℝ} (hx : x ≥ 1) : - log x ≤ x :=
calc - log x ≤ 0 : neg_nonpos.mpr $ log_nonneg hx
        ... ≤ 1 : zero_le_one
        ... ≤ x : hx

lemma one_eventually_le_log : ∀ᶠ (x : ℝ) in filter.at_top, 1 ≤ ∥real.log x∥ :=
begin
  simp only [filter.eventually_at_top, ge_iff_le],
  refine ⟨real.exp 1, λ x hx, _⟩,
  suffices : 1 ≤ real.log x,
  from real.norm_eq_abs (real.log x) ▸ le_abs.2 (or.inl this),
  rwa [← real.log_exp 1, real.log_le_log (real.exp_pos 1) (lt_of_lt_of_le (real.exp_pos 1) hx)],
end

lemma log_ge_of_ge_exp {x y : ℝ} (h : x ≥ real.exp y) : real.log x ≥ y :=
calc y = real.log (real.exp y) : (real.log_exp y).symm
      ... ≤ real.log x : (real.log_le_log (real.exp_pos y) (lt_of_lt_of_le (real.exp_pos y) h)).mpr h

end log_exp

section misc

lemma nnreal.mul_right_le {a b : nnreal} (hb' : b ≤ 1) :
  a * b ≤ a :=
if ha : a = 0 then by simp [ha]
else by rwa [nnreal.mul_le_iff_le_inv ha, inv_mul_cancel ha]

lemma eq_zero_of_norm_fpow_eq_zero {𝕜 : Type*} [normed_field 𝕜] {x : 𝕜} {z : ℤ}
  (hx : ∥x ^ z∥ = 0) : x = 0 :=
fpow_eq_zero (norm_eq_zero.mp hx)

lemma eventually_fpow_ne_zero {α 𝕜 : Type*} [preorder α]
  [normed_field 𝕜] (ι : α → 𝕜)
  (hι : ∀ᶠ (n : α) in filter.at_top, (ι n) ≠ 0) (z : ℤ) : 
  ∀ᶠ (n : α) in filter.at_top, ∥(ι n) ^ z∥ ≠ 0 :=
filter.sets_of_superset _ hι (λ x hx, mt eq_zero_of_norm_fpow_eq_zero hx)

lemma tsum_unique {α β : Type*} [add_comm_monoid α] [topological_space α]
  [t2_space α] [decidable_eq β]
  (f : β → α) (b : β) (hf : ∀ b' ≠ b, f b' = 0) :
  tsum f = f b :=
begin
  refine (tsum_congr (λ b', _)).trans (tsum_ite_eq b (f b)),
  split_ifs with h h,
  { exact congr_arg f h },
  { exact hf _ h }
end

lemma ite_le {A : Type*} [has_le A] {a b c : A} (p : Prop) [decidable p]
  (hab : b ≤ a) (hac : c ≤ a) : ite p b c ≤ a :=
by split_ifs; assumption

section sum_stuff

@[simp]
lemma list.sum_map_neg {G : Type} [add_comm_group G] : 
  ∀ (gs : list G), (gs.map (λ g, -g)).sum = -gs.sum
| [] := by simp
| (h :: t) := by simp [list.sum_map_neg, add_comm (-h)]

@[simp]
lemma list.prod_map_inv {G : Type} [comm_group G] :
  ∀ (gs : list G), (gs.map (λ g, g⁻¹)).prod = gs.prod⁻¹
| [] := by simp
| (h :: t) := by simp [list.prod_map_inv, mul_comm h⁻¹]

lemma list.add_sum_eq_sum_zipwith_drop {G : Type}
  [add_comm_group G] : ∀ (gs gs' : list G),
    gs.sum + gs'.sum = 
      (list.zip_with (λ x y, x + y) gs gs').sum +
        (gs.drop gs'.length).sum +
        (gs'.drop gs.length).sum
| [] gs' := by simp
| (g :: gs) [] := by simp
| (g :: gs) (g' :: gs') := begin
  simp,
  abel,
  rw list.add_sum_eq_sum_zipwith_drop gs gs',
  abel,
end

lemma list.add_sum_eq_sum_zipwith_of_length_eq {G : Type}
  [add_comm_group G] (gs gs' : list G) (h : gs.length = gs'.length) :
    gs.sum + gs'.sum = (list.zip_with (λ x y, x + y) gs gs').sum :=
(list.add_sum_eq_sum_zipwith_drop gs gs').trans (by simp [h])

lemma list.sub_sum_eq_sum_zipwith_drop {G : Type} [add_comm_group G] (gs gs' : list G) :
  gs.sum - gs'.sum =
      (list.zip_with (λ x y, x - y) gs gs').sum +
        (gs.drop gs'.length).sum -
        (gs'.drop gs.length).sum :=
begin
  have : gs.sum - gs'.sum = gs.sum + (gs'.map (λ x, -x)).sum := by simp; abel,
  rw [this, list.add_sum_eq_sum_zipwith_drop gs],
  have : (λ (x : G), has_add.add x ∘ has_neg.neg) = λ x, (λ y, x - y),
  by ext; simp; abel,
  simp [← list.map_drop, list.zip_with_map_right, this],
  abel,
end

lemma list.sum_thing {G : Type} [add_comm_group G] 
  (gs gs' : list G)
  (h : gs.length = gs'.length) :
  gs.sum - gs'.sum = (list.zip_with (λ x y, x - y) gs gs').sum :=
begin
  refine (list.sub_sum_eq_sum_zipwith_drop gs gs').trans _,
  simp [h],
end

lemma list.sum_eq_zero_of_mem_zero {G : Type} [add_group G] :
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
lemma vector.sum_update_nth {G : Type} [add_comm_group G] {n : ℕ}
  (v : vector G n) (i : fin n) (g : G) :
  (v.update_nth i g).to_list.sum = 
    v.to_list.sum - (v.nth i) + g :=
begin
  suffices : v.to_list.sum + ((v.update_nth i g).to_list.sum - v.to_list.sum)
     = v.to_list.sum + (g - (v.nth i)),
  from trans (by abel) (trans this (by abel)),
  refine congr_arg _ _, 
  rw list.sum_thing _,
  { refine list.sum_eq_of_unique _ (g - v.nth i) i.1 _ _,
    { simp, 
      rw list.nth_eq_some,
      refine ⟨by simpa using i.2, _⟩,
      simp,
      },
    { intros m hm hm',
      have hmn : m < n := by simpa using hm,
      rw list.nth_le_zip_with,
      simp,
      rw sub_eq_zero,
      refine vector.nth_update_nth_of_ne _ _,
      refine λ hi, hm' _,
      refine congr_arg (λ (x : fin n), x.1) hi.symm,
    }, },
  simp only [vector.to_list_length],
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
instance list.decidable_subseteq {A : Type} 
  [decidable_eq A] : ∀ (as as' : list A), decidable (as ⊆ as')
| [] as' := is_true (list.nil_subset as')
| (a :: as) as' := by simpa using @and.decidable _ _ _ (list.decidable_subseteq as as')

end misc