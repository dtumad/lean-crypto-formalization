/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.mem
import computational_monads.distribution_semantics.prob_event

/-!
# Repeated Runs of an Oracle Computation

This file defines a construction `repeat oa n` to represent running `oa` independently `n` times,
returning the result as a `vector` of length `n`, by using induction on the input `n`.
-/

namespace oracle_comp

open oracle_spec

variables {α : Type} {spec : oracle_spec} (oa : oracle_comp spec α) (n : ℕ) {m : ℕ}
  (x x' : α) (xs : vector α m) (xs₀ : vector α 0) (xsₛ : vector α (m + 1))

/-- Repeat the computation `oa` independently `n` times to get a length `n` vector of results. -/
def repeat (oa : oracle_comp spec α) : Π (n : ℕ), oracle_comp spec (vector α n)
| 0 := return vector.nil
| (n + 1) := do { a ← oa, as ← repeat n, return (a ::ᵥ as) }

@[simp] lemma repeat_zero : oa.repeat 0 = return vector.nil := rfl

@[simp] lemma repeat_succ : oa.repeat (n + 1) =
  do { a ← oa, as ← repeat oa n, return (a ::ᵥ as) } := rfl

instance repeat.decidable [hoa : oa.decidable] : (oa.repeat n).decidable :=
begin
  induction n with n hn,
  { exact oracle_comp.decidable_return vector.nil },
  { haveI : decidable_eq α := decidable_eq_of_decidable oa,
    refine decidable.decidable_bind' _ _ _ _ hoa (λ _, decidable.decidable_bind' _ _ _ _ hn
      (λ _, decidable.decidable_pure' _ _ (by apply_instance))) }
end

section support

/-- The support of `oa.repeat n` is the set of vectors where every element is in `oa.support`. -/
@[simp] lemma support_repeat : (oa.repeat n).support = {xs | xs.to_list.all₂ (∈ oa.support)} :=
begin
  induction n with n hn,
  { exact set.ext (λ x, by simp only [list.all₂, repeat_zero, support_return, set.set_of_true,
      set.mem_singleton_iff, eq_iff_true_of_subsingleton, vector.to_list_empty, set.mem_univ]) },
  { ext xs,
    obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
    simp only [hn, vector.eq_cons_iff, repeat_succ, support_bind, support_bind_return,
      set.mem_Union, set.mem_image, set.mem_set_of_eq, vector.cons_head, vector.cons_tail,
      exists_eq_right_right, exists_prop, vector.to_list_cons, list.all₂_cons] }
end

lemma mem_support_repeat_iff_all₂ :
  xs ∈ (oa.repeat m).support ↔ xs.to_list.all₂ (∈ oa.support) :=
by rw [support_repeat, set.mem_set_of_eq]

lemma mem_support_repeat_iff_forall :
  xs ∈ (oa.repeat m).support ↔ ∀ x ∈ xs.to_list, x ∈ oa.support :=
by rw [support_repeat, set.mem_set_of_eq, list.all₂_iff_forall]

@[simp] lemma support_repeat_zero : (oa.repeat 0).support = {vector.nil} :=
by simp only [repeat_zero, support_return]

lemma mem_support_repeat_zero : xs₀ ∈ (repeat oa 0).support :=
by simp only [repeat_zero, support_return, set.mem_singleton_iff, eq_iff_true_of_subsingleton]

@[simp] lemma support_repeat_succ : (oa.repeat (n + 1)).support =
  {xs | xs.head ∈ oa.support ∧ xs.tail ∈ (oa.repeat n).support} :=
begin
  refine set.ext (λ xs, _),
  obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
  simpa only [support_repeat, set.mem_set_of_eq, vector.to_list_cons,
    vector.head_cons, vector.tail_cons, list.all₂_cons]
end

lemma mem_support_repeat_succ_iff : xsₛ ∈ (oa.repeat (m + 1)).support ↔
  xsₛ.head ∈ oa.support ∧ xsₛ.tail ∈ (oa.repeat m).support :=
by rw [support_repeat_succ, set.mem_set_of_eq]

@[simp]
lemma cons_mem_support_repeat_succ_iff : (x ::ᵥ xs) ∈ (oa.repeat (m + 1)).support ↔
  x ∈ oa.support ∧ xs ∈ (repeat oa m).support :=
by rw [mem_support_repeat_succ_iff oa (x ::ᵥ xs), vector.head_cons, vector.tail_cons]

lemma mem_support_of_mem_of_support_repeat
  (hxs : xs ∈ (repeat oa m).support) (hx : x ∈ xs.to_list) : x ∈ oa.support :=
by { rw mem_support_repeat_iff_forall at hxs, exact hxs x hx } 

end support

section fin_support

end fin_support

section distribution_semantics

open distribution_semantics

variable [spec.finite_range]

/-- The probability of getting `xs` after `oa.repeat n` is the product of the probability
of getting each individual output, since each computation runs independently. -/
@[simp] lemma eval_dist_repeat_apply [decidable_eq α] :
  ⦃oa.repeat m⦄ xs = (xs.map ⦃oa⦄).to_list.prod :=
begin
  induction m with m hm,
  { simp only [vector.eq_nil xs, repeat_zero oa, eval_dist_return, pmf.pure_apply,
      if_true, vector.map_nil, vector.to_list_nil, list.prod_nil, eq_self_iff_true] },
  { obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
    calc ⦃oa.repeat m.succ⦄ (x ::ᵥ xs)
      = ∑' (y : α) (ys : vector α m), ite (x ::ᵥ xs = y ::ᵥ ys) (⦃oa⦄ y * ⦃oa.repeat m⦄ ys) 0 :
        begin
          simp only [oa.repeat_succ, eval_dist_bind_apply_eq_tsum, eval_dist_return_apply,
            mul_ite, mul_one, mul_zero, ← ennreal.tsum_mul_left],
        end
      ... = ite (x ::ᵥ xs = x ::ᵥ xs) (⦃oa⦄ x * ⦃oa.repeat m⦄ xs) 0 : 
        begin
          rw ← ennreal.tsum_prod,
          refine trans (tsum_eq_single (x, xs) (λ y_ys h, if_neg _)) rfl,
          simp only [ne.def, prod.eq_iff_fst_eq_snd_eq, not_and,
              vector.eq_cons_iff, not_and, vector.head_cons, vector.tail_cons] at h ⊢,
          exact λ h', ne.symm (h h'.symm),
        end
      ... = (vector.map ⦃oa⦄ (x ::ᵥ xs)).to_list.prod :
        begin
          refine (trans (if_pos rfl) _),
          simp only [hm, list.map, vector.to_list_map, vector.to_list_cons, list.prod_cons]
        end }
end

-- begin
--   induction n with n hn,
--   { simp only [vector.eq_nil as, repeat_zero oa, eval_dist_return, pmf.pure_apply,
--       if_true, vector.map_nil, vector.to_list_nil, list.prod_nil, eq_self_iff_true] },
--   { simp_rw [repeat, eval_dist_bind_apply_eq_tsum, ← ennreal.tsum_mul_left],
--     simp [hn],
--     refine trans (tsum_tsum_eq_single _ as.head as.tail _ _) _,
--     { refine λ a h, _,
--       simp only [(vector.ne_cons_iff a as as.tail).2 (or.inl $ ne.symm h), if_false] },
--     { refine λ a as' h, _,
--       simp only [(vector.ne_cons_iff a as as').2 (or.inr $ ne.symm h), if_false] },
--     { split_ifs,
--       { rw [h, vector.to_list_cons, list.map_cons, list.prod_cons],
--         rw [vector.head_cons, vector.tail_cons] },
--       { exact false.elim (h $ symm $ vector.cons_head_tail as) } } }
-- end

end distribution_semantics

end oracle_comp