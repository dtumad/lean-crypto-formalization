/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.constructions.stateless_oracle

/-!
# Coercions Between Coin Oracle to Uniform Select Oracle

This file defines a coercion from a `oracle_comp` for the `coin_spec` spec to a `uniform_select`
oracle, which are in most cases the base oracle for probablistic computation.

The coercion is implemented using the `uniform_of_vector` simulation oracle
with a vector of just `tt` and `ff`, as oposed to `uniform_of_fintype` or `uniform_oracle`,
which avoids use of `noncomputable`.
-/

open oracle_comp oracle_spec 

namespace oracle_comp

/-- coerce a coin flip into a uniform random selection of a `bool` -/
instance coe_coin_uniform_select (α : Type) :
  has_coe (oracle_comp coin_spec α) (oracle_comp uniform_selecting α) :=
{ coe := λ oa, oa.default_simulate' ⟪λ _ _, $ᵛ (tt ::ᵥ ff ::ᵥ vector.nil)⟫ }

variables {α β : Type} (oa : oracle_comp coin_spec α)

lemma coe_coin_uniform_select_def : (↑oa : oracle_comp uniform_selecting α) =
  oa.default_simulate' ⟪λ _ _, $ᵛ (tt ::ᵥ ff ::ᵥ vector.nil)⟫ := rfl

noncomputable instance coe_coin_uniform_select.decidable [hoa : oa.decidable] :
  (↑oa : oracle_comp uniform_selecting α).decidable :=
simulate'.decidable _ _ _

section support

@[simp] lemma support_coe_coin_uniform_select :
  (↑oa : oracle_comp uniform_selecting α).support = oa.support :=
begin
  refine support_simulate'_eq_support _ oa () (λ i t s, _),
  rw [stateless_oracle.apply_eq, support_bind_return, ← set.image_comp,
    set.top_eq_univ, bool.univ_eq, support_uniform_select_vector_cons,
    support_uniform_select_vector_singleton, vector.head_cons, set.image_id', set.union_singleton],
end

@[simp] lemma fin_support_coe_coin_uniform_select [oa.decidable] :
  (↑oa : oracle_comp uniform_selecting α).fin_support = oa.fin_support :=
(fin_support_eq_fin_support_iff_support_eq_support (↑oa : oracle_comp uniform_selecting α) oa).2
  (support_coe_coin_uniform_select oa)

end support

section distribution_semantics

open distribution_semantics

@[simp] lemma eval_dist_coe_coin_uniform_select :
  ⦃(↑oa : oracle_comp uniform_selecting α)⦄ = ⦃oa⦄ :=
begin
  refine eval_dist_simulate'_eq_eval_dist _ oa () (λ i t s, pmf.ext $ λ x, _),
  erw [stateless_oracle.apply_eq, eval_dist_bind_return, pmf.map_comp, pmf.map_id],
  cases x;
  simp only [eval_dist_uniform_select_vector_apply, vector.to_list_cons, vector.to_list_nil,
    pmf.uniform_of_fintype_apply, card_range_coin_spec, list.count_cons, list.count_nil,
    eq_self_iff_true, if_false, if_true, nat.cast_add, nat.cast_one, nat.cast_two, one_div]
end

@[simp] lemma prob_event_coe_coin_uniform_select (e : set α) :
  ⦃e | (↑oa : oracle_comp uniform_selecting α)⦄ = ⦃e | oa⦄ :=
prob_event_eq_of_eval_dist_eq (eval_dist_coe_coin_uniform_select oa) e

end distribution_semantics

end oracle_comp