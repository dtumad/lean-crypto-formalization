import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials 

/-!
# Miscelanious Lemams

This file is a collection of random statements that maybe should eventually move to mathlib.
Most of these are things that could usually be "handwaved" away in proofs. 
-/


lemma finset.to_list_nonempty {A : Type} (s : finset A) (hs : s.nonempty) : ¬ s.to_list.empty :=
let ⟨x, hx⟩ := hs in
  λ h', list.not_mem_nil x ((list.empty_iff_eq_nil.1 h') ▸ (finset.mem_to_list s).2 hx)

section asymptotics

open asymptotics

-- lemma inv_is_O_inv_iff {α 𝕜 𝕜' : Type*} [preorder α] [normed_field 𝕜] [normed_field 𝕜']
--   {l : filter α} {f : α → 𝕜} {g : α → 𝕜'}
--   (hf : ∀ᶠ x in l, ∥f x∥ ≠ 0) (hg : ∀ᶠ x in l, ∥g x∥ ≠ 0) :
--   is_O (λ n, (f n)⁻¹) (λ n, (g n)⁻¹) l ↔ is_O g f l :=
-- begin
--   let hfg := filter.eventually.and hf hg,
--   have hfg : ∀ᶠ x in l, 0 < ∥f x∥ ∧ 0 < ∥g x∥ := begin
--     refine filter.sets_of_superset _ hfg (λ x hx, by simpa using hx),
--   end,
--   simp only [is_O_iff],
--   refine exists_congr (λ c, ⟨λ hc, _, λ hc, _⟩),
--   { refine filter.sets_of_superset _ (hc.and hfg) _,
--     intros x hx,
--     obtain ⟨hx, hx0⟩ := hx,
--     simp_rw [normed_field.norm_inv, inv_eq_one_div, ← mul_div_assoc,
--       mul_one, div_le_iff hx0.1, div_mul_eq_mul_div] at hx,
--     refine (one_le_div hx0.2).1 hx },
--   { refine filter.sets_of_superset _ (hc.and hfg) _,
--     intros x hx,
--     simp_rw [set.mem_set_of_eq, normed_field.norm_inv, inv_eq_one_div, ← mul_div_assoc,
--       mul_one, div_le_iff hx.2.1, div_mul_eq_mul_div],
--     refine (one_le_div hx.2.2).2 hx.1 },
-- end

end asymptotics