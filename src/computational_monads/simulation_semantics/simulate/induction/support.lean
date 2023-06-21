/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.monad
import computational_monads.simulation_semantics.simulate.query

/-!
# Support of Simulations

This file contains more complex lemmas about the support of `simulate` and `simulate'`.
In particular it relates the `support` after `simulate` and `simulate'` to the original `support`,
and gives lemmas for proving equalities between or properties of these `supports`.
-/

variables {α β γ : Type} {spec spec' spec'' : oracle_spec} {S S' : Type}

namespace oracle_comp

open oracle_spec

variables (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S')
  (a : α) (i : spec.ι) (t : spec.domain i) (oa oa' : oracle_comp spec α)
  (ob ob' : α → oracle_comp spec β) (oc : β → oracle_comp spec γ) (s : S) (f : α → β)

section support_eq

/-- Lemma for inductively proving the support of a simulation is a specific function of the input.
Often this is simpler than induction on the computation itself, especially the case of `bind`. -/
lemma support_simulate_eq_induction {supp : Π (α : Type), oracle_comp spec α → S → set (α × S)}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, supp α (return a) s = {(a, s)})
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    supp β (oa >>= ob) s = ⋃ x ∈ (supp α oa s), supp β (ob $ prod.fst x) $ prod.snd x)
  (h_query : ∀ i t s, supp (spec.range i) (query i t) s = (so i (t, s)).support) :
  (simulate so oa s).support = supp α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [h_ret, simulate_return, support_return] },
  { simp only [simulate_bind, support_bind, hoa, hob, h_bind] },
  { simp only [h_query, simulate_query] }
end

/-- Slightly weaker version of `support_simulate_eq_induction` for `simulate'`. -/
lemma support_simulate'_eq_induction {supp : Π (α : Type), oracle_comp spec α → S → set α}
  (so : sim_oracle spec spec' S) (oa : oracle_comp spec α) (s : S)
  (h_ret : ∀ α a s, supp α (return a) s = {a})
  (h_bind : ∀ α β (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) s,
    supp β (oa >>= ob) s = ⋃ x ∈ (simulate so oa s).support, supp β (ob $ prod.fst x) $ prod.snd x)
  (h_query : ∀ i t s, supp (spec.range i) (query i t) s = prod.fst '' (so i (t, s)).support) :
  (simulate' so oa s).support = supp α oa s :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [h_ret, simulate'_return, support_map, support_return, set.image_singleton] },
  { simp only [h_bind, ←hob, simulate'_bind, support_map_bind, support_simulate'] },
  { simp only [h_query, simulate'_query, support_map] }
end

end support_eq

section support_eq_support

/-- If the first output of an oracle can take on any value (although the state might not),
then the first value of simulation has the same support as the original computation.
For example simulation with the identity oracle `idₛ` doesn't change the support,
  and this also holds for something like a logging oracle that just records queries -/
theorem support_simulate'_eq_support (h : ∀ i t s, prod.fst '' (so i (t, s)).support = ⊤) :
  (simulate' so oa s).support = oa.support :=
begin
  refine set.eq_of_subset_of_subset (support_simulate'_subset_support so oa s) (λ x hx, _),
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simpa only [simulate'_return, support_map, support_return, set.image_singleton] using hx },
  { simp only [support_simulate'_bind, support_bind, set.mem_Union] at hx ⊢,
    obtain ⟨a, ha, hx⟩ := hx,
    specialize hoa a ha s,
    rw [support_simulate', set.mem_image] at hoa,
    obtain ⟨⟨a', s'⟩, ha', ha''⟩ := hoa,
    exact ⟨(a', s'), ha', hob a' x (let this : a = a' := ha''.symm in this ▸ hx) s'⟩ },
  { simp only [support_simulate'_query, h i t s] }
end

/-- If the possible outputs of two oracles are the same for any inputs  regardless of their
internal states, then the `support` of `simulate'` with either oracle is the same.
Intuitively the simulations *could* take the same branch at each oracle query, and while the
probabilities of divergence may vary, this doesn't affect the set of possible results. -/
theorem support_simulate'_eq_support_simulate'
  {so : sim_oracle spec spec' S} {so' : sim_oracle spec spec'' S'}
  (h : ∀ i t s s', prod.fst '' (so i (t, s)).support = prod.fst '' (so' i (t, s')).support)
  (oa : oracle_comp spec α) (s : S) (s' : S') :
  (simulate' so oa s).support = (simulate' so' oa s').support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s s',
  { simp only [simulate'_return, support_map, support_return, set.image_singleton] },
  { ext x,
    simp_rw [support_simulate'_bind, set.mem_Union],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨⟨a, t⟩, hoa', hob'⟩ := h,
      have : ∃ u, (a, u) ∈ (simulate so oa s).support := ⟨t, hoa'⟩,
      rw [← mem_support_simulate'_iff_exists_state, hoa s s',
        mem_support_simulate'_iff_exists_state] at this,
      obtain ⟨t', ht'⟩ := this,
      exact ⟨(a, t'), ht', hob a t t' ▸ hob'⟩ },
    { obtain ⟨⟨a, t⟩, hoa', hob'⟩ := h,
      have : ∃ u, (a, u) ∈ (simulate so' oa s').support := ⟨t, hoa'⟩,
      rw [← mem_support_simulate'_iff_exists_state, ← hoa s s',
        mem_support_simulate'_iff_exists_state] at this,
      obtain ⟨t', ht'⟩ := this,
      exact ⟨(a, t'), ht', (hob a t' t).symm ▸ hob'⟩ } },
  { simpa only [support_simulate'_query] using h i t s s' }
end

lemma support_simulate_eq_support_simulate
  (so : sim_oracle spec spec' S) (so' : sim_oracle spec spec'' S)
  (h : ∀ i t s s', (so i (t, s)).support = (so' i (t, s')).support) :
  (simulate so oa s).support = (simulate so' oa s).support :=
begin
  refine support_simulate_eq_induction so oa s _ (λ _ _ _ _ _, _) (λ _ _ _, _),
  { simp only [simulate_return, support_return, eq_self_iff_true, forall_3_true_iff] },
  { simp only [simulate_bind, support_bind, eq_self_iff_true] },
  { rw [simulate_query, h]  }
end

/-- Let `so` and `so'` be two simulation oracles-/
theorem support_simulate_resimulate_eq_support_simulate (so : sim_oracle spec spec' S)
  (so' : sim_oracle spec spec' S) (f : S → S)
  (h : ∀ i t s, (⋃ x ∈ (so i (t, s)).support, (so' i (t, f (prod.snd x))).support) =
    (so i (t, s)).support)
  (oa : oracle_comp spec α) (s : S) :
  (simulate so oa s >>= λ x, simulate so' oa (f x.2)).support = (simulate so oa s).support :=
begin
  sorry
end

/-- Simulating a computation, and then -/
theorem support_simulate_simulate_eq_support_simulate (so so' : sim_oracle spec spec' S)
  (h : ∀ i t s, (⋃ x ∈ (so i (t, s)).support, (so' i (t, prod.snd x)).support) =
    (so i (t, s)).support) (s : S) (oa : oracle_comp spec α) :
  (simulate so oa s >>= λ x, simulate so' oa x.2).support = (simulate so oa s).support :=
begin
  refine symm (support_simulate_eq_induction so oa s (λ α a s, _) _ _),
  { simp only [simulate_return, support_bind_return, support_return, set.image_singleton] },
  { intros α β oa ob s,
    ext x,
    simp,


    sorry },
  { exact h }
end

end support_eq_support

end oracle_comp