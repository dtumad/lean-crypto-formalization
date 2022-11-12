/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.simulate.basic

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
  (ob ob' : α → oracle_comp spec β) (s : S) (f : α → β)

/-- Lemma for inductively proving the support of a simulation is a specific function of the input.
Often this is simpler than induction on the computation itself, especially the case of `bind` -/
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

/-- Since `support` assumes any possible query result, `simulate` will never reduce the support.
In particular the support of a simulation lies in the pullback of the original support. -/
theorem support_simulate_subset_preimage_support :
  (simulate so oa s).support ⊆ prod.fst ⁻¹' oa.support :=
begin
  rw [set.preimage],
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [simulate_return, support_return, set.mem_singleton_iff,
      set.singleton_subset_iff, set.mem_set_of_eq] },
  { rw [support_simulate_bind],
    refine set.Union_subset (λ x, set.Union_subset (λ hx, _)),
    simp only [support_bind, set.mem_Union, exists_prop],
    refine λ b hb, ⟨x.1, hoa s hx, hob x.1 x.2 hb⟩ },
  { simp only [support_query, set.top_eq_univ, set.mem_univ, set.set_of_true, set.subset_univ] }
end

lemma mem_support_of_mem_support_simulate (x : α × S) (hx : x ∈ (simulate so oa s).support) :
  x.1 ∈ oa.support := by simpa using (support_simulate_subset_preimage_support so oa s hx)

/-- Simulation only reduces the possible oracle outputs, so can't reduce the support. In particular
the first output of a simulation has support at most that of the original computation -/
lemma support_simulate'_subset_support : (simulate' so oa s).support ⊆ oa.support :=
begin
  refine (support_simulate' so oa s).symm ▸ λ x hx, _,
  obtain ⟨y, hy, rfl⟩ := (set.mem_image prod.fst _ _).1 hx,
  exact support_simulate_subset_preimage_support so oa s hy,
end

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
  {so : sim_oracle spec spec' S} {so' : sim_oracle spec spec' S'}
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
    -- TODO: This is basically the same as the above, maybe simplify somehow
    { obtain ⟨⟨a, t⟩, hoa', hob'⟩ := h,
      have : ∃ u, (a, u) ∈ (simulate so' oa s').support := ⟨t, hoa'⟩,
      rw [← mem_support_simulate'_iff_exists_state, ← hoa s s',
        mem_support_simulate'_iff_exists_state] at this,
      obtain ⟨t', ht'⟩ := this,
      exact ⟨(a, t'), ht', (hob a t' t).symm ▸ hob'⟩ } },
  { simpa only [support_simulate'_query] using h i t s s' }
end

/-- Given a property `P` of oracle states, if any query call to the oracle preserves it,
then simulation of an entire computation with that oracle will also preserve it. -/
theorem support_state_simulate_induction (so : sim_oracle spec spec' S) (P : S → Prop)
  (s : S) (hs : P s) (oa : oracle_comp spec α) (x : α × S) (hx : x ∈ (simulate so oa s).support)
  (hso : ∀ i t s, ∀ x ∈ (so i (t, s)).support, P s → P (prod.snd x)) : P x.2 :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i' t' generalizing s,
  { rw [support_simulate_return, set.mem_singleton_iff] at hx,
    exact hx.symm ▸ hs },
  { rw [mem_support_simulate_bind] at hx,
    obtain ⟨a, s', ha, ha'⟩ := hx,
    exact hob a x s' (hoa (a, s') s hs ha) ha' },
  { exact hso i' t' s x hx hs }
end

theorem support_simulate_simulate_eq_support_simulate (so so' : sim_oracle spec spec' S)
  (h : ∀ i t s, (⋃ x ∈ (so i (t, s)).support, (so' i (t, prod.snd x)).support) = (so i (t, s)).support)
  (s : S) (oa : oracle_comp spec α) :
  (simulate so oa s >>= λ x, simulate so' oa x.2).support = (simulate so oa s).support :=
begin
  refine symm (support_simulate_eq_induction so oa s _ _ _),
  {
    intros α a s,
    simp only [simulate_return, support_bind_return, support_return, set.image_singleton]
  },
  {

    intros α β oa ob s,
    ext x,
    simp,
    split,
    {
      intro h,
      sorry,
    },
    sorry,
  },
  {
    intros i t s,
    exact h i t s,
  }
end

end oracle_comp