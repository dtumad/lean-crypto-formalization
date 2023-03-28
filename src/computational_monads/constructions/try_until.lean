/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.constructions.repeat

/-!
# Repeated Computation Until a Condition

This file defines a construction `try_until oa p n` that repeats a computation until `p` holds.
The parameter `n` gives a bound on the number of runs (called "gas" in some formulations).
This solves the problem of an unbounded computation, by giving a finite computation depth.
Because this may not always produce a final result, we use an option type to represent failure.

We implement this as a mapping of `oracle_comp.repeat` for simplicity in deriving lemmas.
This means that the computation always "runs" `n` times even if a result is found before that.
However it isn't clear that this is commonly a problem, so we take this approach for now.
-/

namespace oracle_comp

open oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

/-- Computation that repeats `oa` until `p` holds on the result, with at most `n` attempts. -/
def try_until (oa : oracle_comp spec α) (p : α → Prop) [decidable_pred p]
  (n : ℕ) : oracle_comp spec (option α) :=
(λ xs, (vector.to_list xs).find p) <$> (repeat oa n)

variables (oa : oracle_comp spec α) (p : α → Prop) [decidable_pred p] (n : ℕ)

lemma try_until_zero : oa.try_until p 0 =
  (λ xs, (vector.to_list xs).find p) <$> (return vector.nil) := rfl

lemma try_until_succ : oa.try_until p n.succ =
  (λ xs, (vector.to_list xs).find p) <$> do {a ← oa, as ← oa.repeat n, return (a ::ᵥ as)} := rfl

instance try_until.decidable [decidable_eq α] [decidable oa] : decidable (oa.try_until p n) :=
oracle_comp.decidable_map _ _

section support

/-- Any positive result of `oa.try_until p n` will be some output of `oa`. -/
lemma mem_support_of_some_mem_support_try_until (x : α)
  (hx : some x ∈ (oa.try_until p n).support) : x ∈ oa.support :=
begin
  simp_rw [try_until, support_map, set.mem_image, mem_support_repeat_iff_forall] at hx,
  exact let ⟨xs, hxs, hxs'⟩ := hx in hxs x (list.find_mem hxs')
end

/-- Any positive result of `oa.try_until p n` will satisfy the predicate `p`. -/
lemma pos_of_some_mem_support_try_until (x : α)
  (hx : some x ∈ (oa.try_until p n).support) : p x :=
begin
  simp_rw [try_until, support_map, set.mem_image, mem_support_repeat_iff_forall] at hx,
  exact let ⟨xs, hxs, hxs'⟩ := hx in list.find_some hxs',
end

/-- Running a computation zero times will never return a positive result. -/
@[simp] lemma support_try_until_zero : (oa.try_until p 0).support = {none} :=
by rw [try_until_zero, support_map, support_return, set.image_singleton,
  vector.to_list_nil, list.find_nil]

lemma mem_support_try_until_zero_iff (x : option α) : x ∈ (oa.try_until p 0).support ↔ x = none :=
by rw [support_try_until_zero, set.mem_singleton_iff]

/-- `oa.try_until p n` can fail to find a result iff there's an output `x` of `oa` with `¬ p x`. -/
lemma none_mem_support_try_until_succ_iff :
  none ∈ (oa.try_until p n.succ).support ↔ ∃ x ∈ oa.support, ¬ p x :=
begin
  simp only [try_until, mem_support_map_iff, list.find_eq_none],
  exact ⟨λ h, let ⟨xs, hxs, hp⟩ := h in ⟨xs.head, mem_support_of_mem_of_support_repeat hxs
    xs.head_mem, hp _ xs.head_mem⟩, λ h, let ⟨x, hx, hp⟩ := h in ⟨vector.repeat x n.succ,
      repeat_mem_support_repeat n.succ hx, λ y hy, (list.eq_of_mem_repeat hy).symm ▸ hp⟩⟩
end

lemma none_not_mem_support_try_until (hx : ∀ x ∈ oa.support, p x) :
  none ∉ (oa.try_until p n.succ).support :=
mt (none_mem_support_try_until_succ_iff oa p n).1 (by simpa only [not_exists, not_not] using hx)

/-- The possible successful results of `oa.try_until p n` are outputs `x` of `oa` with `p x`. -/
lemma some_mem_support_try_until_succ_iff (x : α) :
  some x ∈ (oa.try_until p n.succ).support ↔ x ∈ oa.support ∧ p x :=
begin
  simp only [try_until, mem_support_map_iff],
  refine ⟨λ h, let ⟨xs, hxs, hp⟩ := h in ⟨mem_support_of_mem_of_support_repeat hxs
    (list.find_mem hp), list.find_some hp⟩, λ h, ⟨vector.repeat x n.succ, repeat_mem_support_repeat
      _ h.1, _⟩,

      ⟩,
  simp only [vector.repeat, list.find_repeat, vector.to_list, h.2],
  simp only [nat.succ_pos', and_self, if_true]
end

lemma some_mem_support_try_until_succ {x : α} (hx : x ∈ oa.support) (h : p x) :
  some x ∈ (oa.try_until p n.succ).support :=
(some_mem_support_try_until_succ_iff oa p n x).2 ⟨hx, h⟩

/-- If at least one result of `oa` doesn't satisfy `p` then the result of `oa.try_until p n.succ`
is either `none` (in the case of failure) or `some x` for some output `x` of `oa` with `p x`. -/
lemma support_try_until_succ_of_exists_neg (h : ∃ x ∈ oa.support, ¬ p x) :
  (oa.try_until p n.succ).support = insert none (option.some '' {x | x ∈ oa.support ∧ p x}) :=
begin
  obtain ⟨x, hx, hpx⟩ := h,
  refine set.ext (λ y, _),
  rw [try_until, support_map, support_repeat_eq_forall],
  cases y with y,
  { simp only [set.mem_image, set.mem_set_of_eq, list.find_eq_none, set.mem_insert_iff,
      eq_self_iff_true, and_false, exists_false, or_false, iff_true],
    refine ⟨vector.repeat x n.succ, λ y hy, _, λ y hy, _⟩;
    { rw [vector.repeat, vector.to_list, list.mem_repeat_succ_iff] at hy,
      simpa only [hy] } },
  { simp only [set.mem_image, set.mem_set_of_eq, set.mem_insert_iff, exists_eq_right, false_or],
    refine ⟨λ h, let ⟨xs, hxs⟩ := h in ⟨hxs.1 _ (list.find_mem hxs.2), list.find_some hxs.2⟩,
    λ h, ⟨vector.repeat y n.succ, λ z hz, _, list.find_cons_of_pos _ h.2⟩⟩,
    rw [vector.repeat, vector.to_list, list.mem_repeat_succ_iff] at hz,
    exact hz.symm ▸ h.1 }
end

/-- If all results of `oa` satisfy `p`, then `oa.try_until p n.succ` will just return `some x`,
for some `x ∈ oa.support`(in particular the result of the first of the `n.succ` runs). -/
lemma support_try_until_succ_of_forall_pos (hp : ∀ x ∈ oa.support, p x) :
  (oa.try_until p n.succ).support = option.some '' oa.support :=
begin
  refine set.ext (λ y, ⟨λ h, _, λ h, _⟩),
  { cases y with y,
    { exact false.elim (none_not_mem_support_try_until oa p n hp h) },
    { exact ⟨y, mem_support_of_some_mem_support_try_until oa p _ y h, rfl⟩ } },
  { exact let ⟨x, hx⟩ := h in hx.2 ▸ some_mem_support_try_until_succ oa p _ hx.1 (hp x hx.1) }
end

end support


end oracle_comp