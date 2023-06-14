/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.vector.mem
import computational_monads.constructions.product
import computational_monads.distribution_semantics.map

/-!
# Repeated Independent Runs of an Oracle Computation

This file defines a construction `repeat oa n` to represent running `oa` independently `n` times,
returning the result as a `vector` of length `n`, by using induction on the input `n`.

`support_repeat_eq_all₂` shows that the possible outputs of `oa.repeat n` are exactly the
vectors such that each element in the vector are possible outputs of `oa`.
`eval_dist_repeat_apply` shows that the probability of getting a given output from `oa.repeat n`
is the product over the vector of the probabilities of getting the individual outputs from `oa`.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Repeat the computation `oa` independently `n` times to get a length `n` vector of results. -/
def repeat (oa : oracle_comp spec α) : Π (n : ℕ), oracle_comp spec (vector α n)
| 0 := return vector.nil
| (n + 1) := do { a ← oa, as ← repeat n, return (a ::ᵥ as) }

variables (oa oa' : oracle_comp spec α) (n : ℕ) {m : ℕ} (x x' : α) (xs : vector α m)
  (xs₀ : vector α 0) (xsₛ : vector α m.succ)

lemma repeat_zero : oa.repeat 0 = return vector.nil := rfl

lemma repeat_succ : oa.repeat n.succ = do {a ← oa, as ← oa.repeat n, return (a ::ᵥ as)} := rfl

section support

/-- The support of `oa.repeat n` is the set of vectors where every element is in `oa.support`. -/
@[simp] theorem support_repeat_eq_all₂ :
  (oa.repeat n).support = {xs | xs.to_list.all₂ (∈ oa.support)} :=
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

lemma support_repeat_eq_forall : (oa.repeat n).support = {xs | ∀ x ∈ xs.to_list, x ∈ oa.support} :=
by simp_rw [support_repeat_eq_all₂, list.all₂_iff_forall]

lemma mem_support_repeat_iff_all₂ : xs ∈ (oa.repeat m).support ↔ xs.to_list.all₂ (∈ oa.support) :=
by rw [support_repeat_eq_all₂, set.mem_set_of_eq]

lemma mem_support_repeat_iff_forall :
  xs ∈ (oa.repeat m).support ↔ ∀ x ∈ xs.to_list, x ∈ oa.support :=
by rw [support_repeat_eq_forall, set.mem_set_of_eq]

@[simp] lemma support_repeat_zero : (oa.repeat 0).support = {vector.nil} :=
by rw [repeat_zero, support_return]

/-- Any empty vector is in the support of a computation that is run zero times. -/
lemma mem_support_repeat_zero : xs₀ ∈ (oa.repeat 0).support :=
by simp only [repeat_zero, support_return, set.mem_singleton_iff, eq_iff_true_of_subsingleton]

/-- The support of running a computation `n + 1` is the set of vectors where the head is in
the computation's support and the tail is in the support of running it `n` times. -/
@[simp] lemma support_repeat_succ : (oa.repeat n.succ).support =
  {xs | xs.head ∈ oa.support ∧ xs.tail ∈ (oa.repeat n).support} :=
begin
  refine set.ext (λ xs, _),
  obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
  simpa only [support_repeat_eq_all₂, set.mem_set_of_eq, vector.to_list_cons,
    vector.head_cons, vector.tail_cons, list.all₂_cons]
end

lemma support_repeat_succ_eq_Union_image : (oa.repeat n.succ).support =
  ⋃ x ∈ oa.support, (vector.cons x) '' (oa.repeat n).support :=
begin
  refine set.ext (λ xs, _),
  obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
  simp_rw [set.mem_Union, support_repeat_succ, set.mem_set_of,
    vector.head_cons, vector.tail_cons, set.mem_image],
  refine ⟨λ h, ⟨x, h.1, xs, h.2, rfl⟩, λ h, _⟩,
  obtain ⟨y, hy, ys, hys, h⟩ := h,
  rw [vector.eq_cons_iff, vector.head_cons, vector.tail_cons] at h,
  refine ⟨h.1 ▸ hy, h.2 ▸ hys⟩,
end

lemma mem_support_repeat_succ_iff : xsₛ ∈ (oa.repeat m.succ).support ↔
  xsₛ.head ∈ oa.support ∧ xsₛ.tail ∈ (oa.repeat m).support :=
by rw [support_repeat_succ, set.mem_set_of_eq]

lemma cons_mem_support_repeat_succ_iff : (x ::ᵥ xs) ∈ (oa.repeat m.succ).support ↔
  x ∈ oa.support ∧ xs ∈ (oa.repeat m).support :=
by rw [mem_support_repeat_succ_iff oa, vector.head_cons, vector.tail_cons]

/-- If a vector is in the support of `oa.repeat m` then any of its members is in `oa.support`. -/
lemma mem_support_of_mem_of_support_repeat {oa : oracle_comp spec α} {x : α} {xs : vector α m}
  (hxs : xs ∈ (oa.repeat m).support) (hx : x ∈ xs.to_list) : x ∈ oa.support :=
by { rw mem_support_repeat_iff_forall at hxs, exact hxs x hx }

lemma replicate_mem_support_repeat {oa : oracle_comp spec α} {x : α} (n : ℕ) (hx : x ∈ oa.support) :
  vector.replicate n x ∈ (oa.repeat n).support :=
by { rw [mem_support_repeat_iff_forall], exact (λ y hy, (list.eq_of_mem_replicate hy).symm ▸ hx) }

end support

section fin_support

lemma mem_fin_support_repeat_iff_all₂ :
  xs ∈ (oa.repeat m).fin_support ↔ xs.to_list.all₂ (∈ oa.fin_support) :=
by simp only [mem_fin_support_iff_mem_support, mem_support_repeat_iff_all₂]

lemma mem_fin_support_repeat_iff_forall :
  xs ∈ (oa.repeat m).fin_support ↔ ∀ x ∈ xs.to_list, x ∈ oa.fin_support :=
by simp only [mem_fin_support_iff_mem_support, mem_support_repeat_iff_forall]

end fin_support

section eval_dist

/-- The probability of getting `xs` after `oa.repeat n` is the product of the probability
of getting each individual output, since each computation runs independently. -/
@[simp] theorem eval_dist_repeat_apply : ⁅= xs | oa.repeat m⁆ = (xs.to_list.map ⁅oa⁆).prod :=
begin
  induction m with m hm,
  { simp only [vector.eq_nil xs, repeat_zero oa, eval_dist_return, pmf.pure_apply,
      if_true, list.map_nil, vector.to_list_nil, list.prod_nil, eq_self_iff_true] },
  { obtain ⟨x, xs, rfl⟩ := vector.exists_eq_cons xs,
    calc ⁅oa.repeat m.succ⁆ (x ::ᵥ xs) =
      ∑' y ys, ⁅oa⁆ y * ⁅oa.repeat m⁆ ys * set.indicator {y ::ᵥ ys} (λ _, 1) (x ::ᵥ xs) :
        by simp only [repeat_succ, eval_dist_bind_apply_eq_tsum, ← ennreal.tsum_mul_left,
          eval_dist_return_apply_eq_indicator, hm, list.map, vector.to_list_map,
          vector.to_list_cons, list.prod_cons, mul_assoc]
      ... = ⁅oa⁆ x * ⁅oa.repeat m⁆ xs * set.indicator {x ::ᵥ xs} (λ _, 1) (x ::ᵥ xs) :
        begin
          refine tsum_tsum_eq_single _ x xs (λ y hy, mul_eq_zero_of_right _ $
            set.indicator_apply_eq_zero.2 (λ h, (hy _).elim)) (λ y ys hys, mul_eq_zero_of_right _ $
            set.indicator_apply_eq_zero.2 (λ h, (hys _).elim)),
          { rw [set.mem_singleton_iff, vector.eq_cons_iff, vector.head_cons, vector.tail_cons] at h,
            exact h.1.symm },
          { rw [set.mem_singleton_iff, vector.eq_cons_iff, vector.head_cons, vector.tail_cons] at h,
            exact h.2.symm }
        end
      ... = ⁅oa⁆ x * ⁅oa.repeat m⁆ xs :
        by simp only [set.indicator_of_mem, set.mem_singleton, mul_one]
      ... = ((x ::ᵥ xs).to_list.map ⁅oa⁆).prod :
        by rw [vector.to_list_cons, list.map_cons, list.prod_cons, hm] }
end

lemma eval_dist_repeat_zero' : ⁅oa.repeat 0⁆ = ⁅(return vector.nil : oracle_comp spec _)⁆ := rfl

@[simp] lemma eval_dist_repeat_zero : ⁅oa.repeat 0⁆ = pmf.pure vector.nil :=
by simp only [repeat_zero, eval_dist_return]

lemma eval_dist_repeat_zero_apply : ⁅oa.repeat 0⁆ xs₀ = 1 :=
by simp only [repeat_zero, eval_dist_return, pmf.pure_apply, eq_iff_true_of_subsingleton, if_true]

@[simp_dist_equiv]
lemma repeat_succ_dist_equiv : oa.repeat n.succ ≃ₚ (λ (x : α × vector α n), x.1 ::ᵥ x.2) <$> (oa ×ₘ oa.repeat n) :=
by rw [dist_equiv.def, repeat_succ, map_eq_bind_return_comp, (prod_bind_equiv_bind_bind _ _ _).eval_dist_eq]

lemma eval_dist_repeat_succ' :
  ⁅oa.repeat n.succ⁆ = ⁅(λ (x : α × vector α n), x.1 ::ᵥ x.2) <$> (oa ×ₘ oa.repeat n)⁆ :=
by rw [repeat_succ, map_eq_bind_return_comp, (prod_bind_equiv_bind_bind _ _ _).eval_dist_eq]

@[simp] lemma eval_dist_repeat_succ :
  ⁅oa.repeat n.succ⁆ = ⁅oa ×ₘ oa.repeat n⁆.map (λ x, x.1 ::ᵥ x.2) :=
(oa.eval_dist_repeat_succ' n).trans (eval_dist_map _ _)

lemma eval_dist_repeat_succ_apply :
  ⁅oa.repeat m.succ⁆ xsₛ = ⁅oa⁆ xsₛ.head * ⁅oa.repeat m⁆ xsₛ.tail :=
calc ⁅oa.repeat m.succ⁆ xsₛ = ⁅(λ (x : α × vector α m), x.1 ::ᵥ x.2) <$> (oa ×ₘ oa.repeat m)⁆ xsₛ :
    by rw eval_dist_repeat_succ' oa m
  ... = ⁅oa ×ₘ oa.repeat m⁆ (xsₛ.head, xsₛ.tail) :
    eval_dist_map_apply_eq_single' _ _ (xsₛ.head, xsₛ.tail) xsₛ (xsₛ.cons_head_tail)
      (λ x hx hx', by rw [← hx', vector.head_cons, vector.tail_cons, prod.mk.eta])
  ... = ⁅oa⁆ xsₛ.head * ⁅oa.repeat m⁆ xsₛ.tail : by rw eval_dist_product_apply

section tomove

lemma bind_dist_equiv_right (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (x : α) (h : ∀ x' ∈ oa.support, ob x' ≃ₚ ob x) : oa >>= ob ≃ₚ ob x :=
begin
  refine (dist_equiv.ext (λ y, _)),
  calc ⁅= y | oa >>= ob⁆ = ∑' x', ⁅= x' | oa⁆ * ⁅= y | ob x'⁆ : eval_dist_bind_apply_eq_tsum _ _ y
    ... = ∑' x', ⁅= x' | oa⁆ * ⁅= y | ob x⁆ : begin
      refine tsum_congr (λ x', _),
      by_cases hx' : x' ∈ oa.support,
      { rw [(h _ hx').eval_dist_apply_eq] },
      { simp_rw [eval_dist_eq_zero hx', zero_mul] }
    end
    ... = ⁅= y | ob x⁆ : by rw [ennreal.tsum_mul_right, ⁅oa⁆.tsum_coe, one_mul]
end

lemma bind_dist_equiv_left (oa : oracle_comp spec α) (oa' : α → oracle_comp spec α)
  (h : ∀ x ∈ oa.support, oa' x ≃ₚ (return x : oracle_comp spec α)) : oa >>= oa' ≃ₚ oa :=
begin
  refine trans (bind_dist_equiv_bind_of_dist_equiv_right _ _ _ h) (bind_return_id_dist_equiv _),
end

lemma dist_equiv_return_iff (oa : oracle_comp spec α) (x : α) :
  oa ≃ₚ (return x : oracle_comp spec' α) ↔ oa.support = {x} :=
begin
  refine ⟨λ h, h.support_eq.trans (support_return _ _), λ h, dist_equiv.ext (λ y, _)⟩,
  by_cases hy : y = x,
  { rwa [hy, eval_dist_return_apply_self, eval_dist_eq_one_iff] },
  { rwa [eval_dist_return_apply_of_ne _ hy, eval_dist_eq_zero_iff, h, set.mem_singleton_iff] }
end

lemma map_bind_dist_equiv_left (f : β → α) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
  (h : ∀ x ∈ oa.support, f '' (ob x).support = {x}) : f <$> (oa >>= ob) ≃ₚ oa :=
begin
  refine trans (map_bind_dist_equiv _ _ _) _,
  apply bind_dist_equiv_left,
  intros x hx,
  rw [dist_equiv_return_iff, support_map, h x hx],
end

lemma map_bind_dist_equiv_right {f : β → γ} {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  (x : α) (h : ∀ y ∈ oa.support, f <$> ob y ≃ₚ f <$> ob x) :
  f <$> (oa >>= ob) ≃ₚ f <$> (ob x) :=
begin
  refine trans (map_bind_dist_equiv _ _ _) _,
  apply bind_dist_equiv_right,
  exact h,
end

end tomove

@[simp_dist_equiv]
lemma map_nth_repeat_dist_equiv (i : fin m) : (λ xs, vector.nth xs i) <$> oa.repeat m ≃ₚ oa :=
begin
  haveI : inhabited α := ⟨oa.default_result⟩,
  induction m with m hm,
  { exact fin.elim0 i },
  { by_cases hi : i = 0,
    { simp only [hi, repeat_succ, vector.nth_zero],
      refine map_bind_dist_equiv_left _ _ _ (λ x hx, _),
      rw [← support_map, support_eq_singleton_iff_forall],
      intros y hy,
      simp at hy,
      exact hy.2 },
    { suffices : ∀ x, (λ xs, vector.nth xs i) <$> (oa.repeat m >>= λ xs, return (x ::ᵥ xs)) ≃ₚ
        (λ xs, vector.nth xs (i.pred hi)) <$> oa.repeat m,
      from trans (trans (map_bind_dist_equiv_right default
        (λ y hy, (this y).trans (this _).symm)) (this default)) (hm $ i.pred hi),
      refine λ x, (map_comp_dist_equiv _ _ _).trans _,
      pairwise_dist_equiv,
      simp only [function.comp_app, pure'_eq_return, return_dist_equiv_return_iff],
      exact (trans (congr_arg _ (fin.succ_pred _ _).symm) (vector.nth_cons_succ x _ _)) } }
end

@[simp_dist_equiv]
lemma map_head_repeat_dist_equiv : vector.head <$> oa.repeat m.succ ≃ₚ oa :=
calc vector.head <$> oa.repeat m.succ ≃ₚ (λ xs, vector.nth xs 0) <$> oa.repeat m.succ :
  by simp only [vector.nth_zero] ... ≃ₚ oa : by pairwise_dist_equiv

@[simp] lemma eval_dist_map_nth_repeat_apply (i : fin m) (x : α) :
  ⁅= x | (λ xs, vector.nth xs i) <$> oa.repeat m⁆ = ⁅= x | oa⁆ :=
dist_equiv.eval_dist_apply_eq (by pairwise_dist_equiv) x

lemma repeat_dist_equiv_repeat_of_dist_equiv (h : oa ≃ₚ oa') : oa.repeat n ≃ₚ oa'.repeat n :=
begin
  induction n with n hn,
  pairwise_dist_equiv,
  simp_rw [repeat_succ],
  pairwise_dist_equiv [h, hn],
end

end eval_dist

section prob_event

@[simp] lemma prob_event_repeat (e : set (vector α m)) :
  ⁅e | oa.repeat m⁆ = ∑' (xs : vector α m), e.indicator (λ xs, (xs.to_list.map ⁅oa⁆).prod) xs :=
(prob_event_eq_tsum_indicator _ e).trans (tsum_congr (λ x,
  by simp only [set.indicator, eval_dist_repeat_apply]))

lemma prob_event_succ_thing (e : set (vector α m.succ)) :
  ⁅e | oa.repeat m.succ⁆ = ∑' (x : α) (xs : vector α m), e.indicator (λ ys, (ys.to_list.map ⁅oa⁆).prod) (x ::ᵥ xs) :=
by simp only [prob_event_repeat, ennreal.tsum_vector_succ]

/-- After repeating a computation the probability of an event holding on any single
result is the same as the probability of the event holding after running the computation once. -/
@[simp] lemma prob_event_nth_repeat (e : set α) (i : fin m) :
  ⁅λ xs, xs.nth i ∈ e | oa.repeat m⁆ = ⁅e | oa⁆ :=
trans (by simpa only [prob_event_map])
  (prob_event_eq_of_eval_dist_eq (map_nth_repeat_dist_equiv oa i) e)

@[simp] lemma prob_event_head_repeat (e : set α) :
  ⁅λ xs, xs.head ∈ e | oa.repeat m.succ⁆ = ⁅e | oa⁆ :=
calc ⁅λ xs, xs.head ∈ e | oa.repeat m.succ⁆ = ⁅λ xs, xs.nth 0 ∈ e | oa.repeat m.succ⁆ :
    by simp only [vector.nth_zero]
  ... = ⁅e | oa⁆ : prob_event_nth_repeat oa e 0

/-- For any output `xs` of `oa.repeat m` the probability that all elements of `xs` satisfy `p`
is the probability of a single output of `oa` satisfying `p` raised to the `m`. -/
@[simp] lemma prob_event_all₂ (p : α → Prop) :
  ⁅λ xs, xs.to_list.all₂ p | oa.repeat m⁆ = ⁅p | oa⁆ ^ m :=
begin
  induction m with m hm,
  { simp only [pow_zero, prob_event_eq_one_iff_support_subset,
      support_repeat_zero, set.singleton_subset_iff] },
  { rw [pow_succ, ← hm],
    simp only [repeat_succ, prob_event_bind_eq_tsum, prob_event_bind_return],
    rw [prob_event_eq_tsum_indicator, ← ennreal.tsum_mul_right],
    refine tsum_congr (λ x, _),
    by_cases hx : p x,
    { rw [set.indicator_apply_eq_self.2 (λ h, (h hx).elim)],
      refine congr_arg ((*) ⁅= x | oa⁆) (prob_event_eq_of_mem_iff _ _ _ (λ xs, _)),
      show list.all₂ p (x ::ᵥ xs).to_list ↔ list.all₂ p xs.to_list,
      by simp [hx] },
    { simp only [set.indicator_apply_eq_zero.2 (λ h, (hx h).elim), zero_mul, mul_eq_zero,
        eval_dist_eq_zero_iff, prob_event_eq_zero_iff_disjoint_support, support_repeat_eq_all₂,
        or_iff_not_imp_left, not_not],
      refine λ hx', set.disjoint_iff_forall_ne.2 (λ ys hys zs hzs, _),
      have : list.all₂ p (x ::ᵥ zs).to_list := hzs,
      rw [vector.to_list_cons, list.all₂_cons] at this,
      refine (hx this.1).elim } }
end

end prob_event

end oracle_comp