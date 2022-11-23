/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.tracking_oracle
import computational_monads.support.prod

/-!
# Stateless Oracles

This file defines a specific version of `tracking_oracle`, where the tracking isn't used.
This allows a specified function for responding to queries,
making no use of the internal state (which is left as a `unit` type).
-/

open oracle_comp oracle_spec

variables {α β : Type} {spec spec' spec'' : oracle_spec}

/-- Simulate a computation without making use of the internal state.
  We use the `unit` type as the state in this case, so all possible states are equal.
  Implemented as a `tracking_oracle` where the state isn't actually tracking anything -/
def stateless_oracle (spec spec' : oracle_spec)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)) :
  sim_oracle spec spec' unit :=
⟪o | λ _ _ _ _, (), ()⟫

notation `⟪` o `⟫` := stateless_oracle _ _ o

namespace stateless_oracle

variables (oa : oracle_comp spec α)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i))

@[simp]
lemma apply_eq (i : spec.ι) (t : spec.domain i) (s : unit) :
  ⟪o⟫ i (t, s) = o i t >>= λ u, return (u, ()) := rfl

instance decidable [spec.computable] [∀ i x, (o i x).decidable] (i : spec.ι)
  (x : spec.domain i × unit) : (⟪o⟫ i x).decidable :=
tracking_oracle.decidable o _ _ i x

section support

lemma support_apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  (⟪o⟫ i (t, s)).support = prod.fst ⁻¹' (o i t).support :=
by simp only [apply_eq, support_bind_prod_mk_fst_id_of_subsingleton]

-- TODO: this should generalize I think?
lemma fin_support_apply [spec'.computable] [spec'.finite_range] [spec.computable]
  [∀ i x, (o i x).decidable]
  (i : spec.ι) (t : spec.domain i) (s : unit) (x : spec.range i × unit) :
  (⟪o⟫ i (t, s)).fin_support = finset.preimage (o i t).fin_support prod.fst
    (λ y hy z hz h, prod.eq_iff_fst_eq_snd_eq.2 ⟨h, punit_eq _ _⟩) :=
begin

end

lemma mem_fin_support_apply [spec'.computable] [spec'.finite_range] [spec.computable]
  [∀ i x, (o i x).decidable]
  (i : spec.ι) (t : spec.domain i) (s : unit) (x : spec.range i × unit) :
  x ∈ (⟪o⟫ i (t, s)).fin_support ↔ x.1 ∈ (o i t).fin_support :=
sorry

lemma mem_support_apply_iff (i : spec.ι) (t : spec.domain i) (s s' : unit) (u : spec.range i) :
  (u, s') ∈ (⟪o⟫ i (t, s)).support ↔ u ∈ (o i t).support :=
by simp only [apply_eq, support_bind, support_return, set.mem_Union, set.mem_singleton_iff,
  prod.mk.inj_iff, eq_iff_true_of_subsingleton, and_true, exists_prop, exists_eq_right']

lemma support_simulate_eq_support_default_simulate (oa : oracle_comp spec α) (s : unit) :
  (oa.simulate ⟪o⟫ s).support = (oa.default_simulate ⟪o⟫).support := punit_eq () s ▸ rfl

lemma support_simulate_eq_preimage_default_simulate' (oa : oracle_comp spec α) (s : unit) :
  (oa.simulate ⟪o⟫ s).support = prod.fst ⁻¹' (oa.default_simulate' ⟪o⟫).support :=
begin
  rw [default_simulate', punit_eq ⟪o⟫.default_state s, simulate', support_map],
  exact (set.preimage_image_eq _ prod.fst_injective).symm
end

@[simp] lemma mem_support_simulate_iff (oa : oracle_comp spec α) (s : unit) (x : α × unit) :
  x ∈ (oa.simulate ⟪o⟫ s).support ↔ x.1 ∈ (oa.default_simulate' ⟪o⟫).support :=
by rw [support_simulate_eq_preimage_default_simulate', set.mem_preimage]

@[simp] lemma support_simulate' (oa : oracle_comp spec α) (s : unit) :
  (oa.simulate' ⟪o⟫ s).support = (oa.default_simulate' ⟪o⟫).support :=
congr_arg _ (congr_arg _ (punit_eq _ _))

@[simp]
lemma mem_support_simulate'_iff (oa : oracle_comp spec α) (s : unit) (x : α) :
  x ∈ (oa.simulate' ⟪o⟫ s).support ↔ x ∈ (oa.default_simulate' ⟪o⟫).support :=
by rw [support_simulate']

@[simp]
lemma support_default_simulate_eq_preimage (oa : oracle_comp spec α) :
  (oa.default_simulate ⟪o⟫).support = prod.fst ⁻¹' (oa.default_simulate' ⟪o⟫).support :=
support_simulate_eq_preimage_default_simulate' o oa ()

@[simp]
lemma mem_support_default_simulate_iff (oa : oracle_comp spec α) (x : α × unit) :
  x ∈ (oa.default_simulate ⟪o⟫).support ↔ x.1 ∈ (oa.default_simulate' ⟪o⟫).support :=
mem_support_simulate_iff o oa () x

section return

lemma support_simulate_return (a : α) (s : unit) :
  (simulate ⟪o⟫ (return a) s).support = {(a, ())} := 
by {induction s, refl}

end return

section bind

@[simp]
lemma support_simulate_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (s : unit) :
  (simulate ⟪o⟫ (oa >>= ob) s).support =
    ⋃ (x : α) (hx : (x, ()) ∈ (simulate ⟪o⟫ oa ()).support),
      (simulate ⟪o⟫ (ob x) ()).support :=
begin
  rw [support_simulate_eq_preimage_default_simulate'],
  sorry
end

-- TODO: full API
@[simp]
lemma support_default_simulate'_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (default_simulate' ⟪o⟫ (oa >>= ob)).support =
    ⋃ a ∈ (default_simulate' ⟪o⟫ oa).support, (default_simulate' ⟪o⟫ (ob a)).support :=
begin
  rw [default_simulate', simulate', support_map],
  sorry,
end

end bind

section query

@[simp]
lemma support_simulate_query (i : spec.ι) (t : spec.domain i) (s : unit) :
  (simulate ⟪o⟫ (query i t) s).support = {x | x.1 ∈ (o i t).support} :=
begin
  refine s.rec _,
  simp,
  sorry,
end

@[simp]
lemma support_default_simulate'_query (i : spec.ι) (t : spec.domain i) :
  (default_simulate' ⟪o⟫ (query i t)).support = (o i t).support :=
sorry

end query

end support

section distribution_semantics

section eval_dist

end eval_dist

open distribution_semantics

section equiv

-- TODO: put <$> in equiv versions, derive from `eval_dist` fact
lemma simulate_equiv_simulate' [spec'.finite_range] (s : unit) :
  simulate ⟪o⟫ oa s ≃ₚ (simulate' ⟪o⟫ oa s >>= λ a, return (a, ())) :=
calc simulate ⟪o⟫ oa s ≃ₚ simulate ⟪o⟫ oa s >>= return : symm (bind_return_equiv _)
  ... ≃ₚ simulate ⟪o⟫ oa s >>= λ x, return (x.1, x.2) : by simp only [prod.mk.eta]
  ... ≃ₚ simulate ⟪o⟫ oa s >>= λ x, return (x.1, ()) : 
    bind_equiv_of_equiv_second _ (λ x, by simp [punit_eq x.snd ()])
  ... ≃ₚ simulate' ⟪o⟫ oa s >>= λ a, return (a, ()) : by rw [simulate', bind_map_equiv]

lemma simulate'_equiv_of_oracle_equiv [spec'.finite_range] [spec''.finite_range] 
  {o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)}
  {o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i)}
  (s : unit) (h : ∀ (i : spec.ι) (t : spec.domain i), o i t ≃ₚ o' i t) :
  simulate' ⟪o⟫ oa s ≃ₚ simulate' ⟪o'⟫ oa s :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  sorry, sorry, sorry
  -- { simp only [simulate'_return, map_return_equiv, eval_dist_return] },
  -- { calc simulate' ⟪o⟫ (oa >>= ob) s
  --     ≃ₚ simulate ⟪o⟫ oa s >>= λ x, simulate' ⟪o⟫ (ob x.1) x.2 :
    --simulate'_bind_equiv ⟪o⟫ oa ob _
  --     ... ≃ₚ simulate ⟪o'⟫ oa s >>= λ x, simulate' ⟪o'⟫ (ob x.1) x.2 : begin
  --       simp [simulate_equiv_simulate', hoa],
  --       -- congr,
  --       simpa [hob],
  --     end
  --     ... ≃ₚ simulate' ⟪o'⟫ (oa >>= ob) s : symm (simulate'_bind_equiv ⟪o'⟫ oa ob _) },
  -- { simp_rw [simulate'_query_equiv, stateless_oracle.apply_eq, fst_map_bind_mk_equiv],
  --   exact map_equiv_of_equiv _ (h i t), },
end 

lemma simulate'_query_equiv [spec.finite_range] (s : unit) :
  simulate' ⟪query⟫ oa s ≃ₚ oa :=
tracking_oracle.eval_dist_simulate'_query_eq_eval_dist _ _ oa s

lemma simulate'_query_equiv_of_equiv [spec.finite_range] [spec'.finite_range] (s : unit)
  (ho : ∀ (i : spec.ι) (t : spec.domain i), o i t ≃ₚ query i t) :
  simulate' ⟪o⟫ oa s ≃ₚ oa :=
calc simulate' ⟪o⟫ oa s ≃ₚ simulate' ⟪query⟫ oa s
    : simulate'_equiv_of_oracle_equiv oa s ho
  ... ≃ₚ oa : simulate'_query_equiv oa s

end equiv

section prob_event


end prob_event

end distribution_semantics

end stateless_oracle

-- More lemmas we can prove about `tracking_oracle` with the definition of the `stateless_oracle`
namespace tracking_oracle

variables {S S' : Type} (o o' : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (update_state update_state': Π (s : S) (i : spec.ι), spec.domain i → spec.range i → S)
  (default_state default_state' s s' : S) (oa : oracle_comp spec α)

section support

/-- The first output with a tracking oracle is independent of any of the tracking state -/
lemma support_simulate'_eq_support_simulate'_stateless_oracle :
  (simulate' ⟪o | update_state, default_state⟫ oa s).support = (simulate' ⟪o⟫ oa ()).support :=
begin
  sorry
  -- unfold stateless_oracle,
  -- refine support_simulate'_eq_of_oracle_eq o update_state (λ _ _ _ _, ()) default_state _ oa s _
end

end support

section distribution_semantics

open distribution_semantics

/-- The first output of a tracking oracle is equivalent to using just the stateless oracle -/
theorem simulate'_equiv_stateless_oracle [spec'.finite_range] :
  simulate' ⟪o | update_state, default_state⟫ oa s ≃ₚ
    simulate' ⟪o⟫ oa () :=
begin
  sorry
  -- induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  -- { simp },
  -- { let so := ⟪o|update_state, default_state⟫,
  --   calc simulate' so (oa >>= ob) s
  --     ≃ₚ (simulate so oa s) >>= (λ x, simulate' so (ob x.1) x.2) :
              --simulate'_bind_equiv so oa ob s
  --     ... ≃ₚ (simulate so oa s) >>= (λ x, simulate' ⟪o⟫ (ob x.1) ()) :
  --       bind_equiv_of_equiv_second _ (λ a, (hob a.1 a.2))
  --     ... ≃ₚ (simulate' so oa s) >>= (λ x, simulate' ⟪o⟫ (ob x) ()) : by erw [bind_map_equiv]
  --     ... ≃ₚ (simulate' ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x) ()) :
  --       bind_equiv_of_equiv_first _ (hoa _)
  --     ... ≃ₚ (simulate ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x.1) ()) : by erw [bind_map_equiv]
  --     ... ≃ₚ (simulate ⟪o⟫ oa ()) >>= (λ x, simulate' ⟪o⟫ (ob x.1) x.2) :
  --       by { congr, ext x, rw [punit_eq () x.2] }
  --     ... ≃ₚ simulate' ⟪o⟫ (oa >>= ob) () : by rw [simulate'_bind_equiv] },
  -- { simp_rw [simulate'_query_equiv, apply_eq, stateless_oracle.apply_eq, map_bind_equiv],
  --   refine bind_equiv_of_equiv_second (o i t) _,
  --   simp only [map_pure_equiv, eq_self_iff_true, forall_const] }
end

/-- The first ouptput of a tracking oracle is indepenedent of the actual tracking functions -/
lemma simulate'_equiv_of_equiv [spec'.finite_range] (h : ∀ i t, o i t ≃ₚ o' i t) :
  simulate' ⟪o | update_state, default_state⟫ oa s ≃ₚ
    simulate' ⟪o' | update_state', default_state'⟫ oa s' :=
calc simulate' ⟪o | update_state, default_state⟫ oa s
  ≃ₚ simulate' ⟪o⟫ oa () : simulate'_equiv_stateless_oracle o update_state default_state s oa
  ... ≃ₚ simulate' ⟪o'⟫ oa () : stateless_oracle.simulate'_equiv_of_oracle_equiv oa () h
  ... ≃ₚ simulate' ⟪o' | update_state', default_state'⟫ oa s' :
    symm (simulate'_equiv_stateless_oracle o' update_state' default_state' _ _)

end distribution_semantics

end tracking_oracle