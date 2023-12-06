/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.is_stateless

/-!
# Coercions Between Computations With Additional Oracles

This file defines a `is_sub_spec` relation for pairs of `oracle_spec` where one can be
thought of as an extension of the other with additional oracles.
The definition consists of a function from query inputs in the original oracle to a
computation using the new set of oracles, such that the result of the mapping
doesn't affect the underlying probability distribution on the oracle call.

We use the notation `spec ⊂ₒ spec'` to represent that one set of oracles is a subset of another,
where the non-exclusive subset symbol reflects that we avoid defining this instance reflexively.
This decision is based on the `is_coe` construction, where we don't want to coerce a computation
to itself by calling a reflexive `is_sub_spec` construction.

We define the map to output a computation rather than a new set of oracle inputs in the new spec
to avoid type checking issues, as the `query` output type will not be definitionally equal
to the `query` output type in the original `oracle_spec`, causing issues in defining `has_coe`.
In practice the mapping will still usually output a `query` call,
and the equality between the underlying distributions is generally sufficient.

From this definition we construct a `is_coe` instance to coerce a computation with one set of
oracles to one with a larger set of oracles, using the `is_sub_spec` to call `simulate'`.
We show that this coercion has no effect on `support`, `eval_dist`, or `prob_event`.
-/

variables {α β γ : Type}

namespace oracle_spec

open oracle_comp

/-- Example of a computation that naturally should work, but doesn't without `sub_spec` coercions.
The fundamental issue being that the type system doesn't have a sense of "additional" oracles.
In this case, performing a validity check on the adversaries results isn't easily possible.
Note the actual version is commented out, only the un-checked version will compile. -/
noncomputable example {regular_spec adversary_spec : oracle_spec}
  (adversary : oracle_comp (regular_spec ++ adversary_spec) α)
  (validity_check : α → oracle_comp regular_spec bool) :
  oracle_comp (regular_spec ++ adversary_spec) (option α) :=
-- do { x ← adversary, b ← validity_check x, return (if b = tt then some x else none) }
do { x ← adversary, return x }

/-- Relation defining an inclusion of one set of oracles into another, where the mapping
doesn't affect the underlying probability distribution of the computation.
Informally, `sub_spec ⊂ₒ super_spec` means that for any query to an oracle of `sub_spec`,
it can be perfectly simulated by a computation using the oracles of `super_spec`. -/
class is_sub_spec (sub_spec super_spec : oracle_spec) :=
(to_fun (i : sub_spec.ι) (t : sub_spec.domain i) : oracle_comp super_spec (sub_spec.range i))
(to_fun_equiv : ∀ i t, to_fun i t ≃ₚ query i t)

infixl ` ⊂ₒ `:65 := is_sub_spec

namespace is_sub_spec

variables (sub_spec super_spec : oracle_spec) [h : sub_spec ⊂ₒ super_spec]
  (i : sub_spec.ι) (t : sub_spec.domain i)

@[pairwise_dist_equiv] lemma to_fun_dist_equiv : h.to_fun i t ≃ₚ query i t := h.to_fun_equiv i t

@[simp] lemma support_to_fun : (h.to_fun i t).support = set.univ :=
(h.to_fun_equiv i t).support_eq.trans (support_query i t)

@[simp] lemma fin_support_to_fun : (h.to_fun i t).fin_support = finset.univ :=
(h.to_fun_equiv i t).fin_support_eq.trans (fin_support_query i t)

@[simp] lemma eval_dist_to_fun : ⁅h.to_fun i t⁆ = pmf.uniform_of_fintype (sub_spec.range i) :=
(h.to_fun_equiv i t).eval_dist_eq.trans (eval_dist_query i t)

lemma prob_output_to_fun_eq_div (u : sub_spec.range i) :
  ⁅= u | h.to_fun i t⁆ = 1 / fintype.card (sub_spec.range i) :=
((h.to_fun_equiv i t).prob_output_eq u).trans (prob_output_query_eq_div i t u)

lemma prob_output_to_fun_eq_inv (u : sub_spec.range i) :
  ⁅= u | h.to_fun i t⁆ = (fintype.card (sub_spec.range i))⁻¹ :=
((h.to_fun_equiv i t).prob_output_eq u).trans (prob_output_query_eq_inv i t u)

@[simp] lemma prob_event_to_fun_eq_div (e : set (sub_spec.range i)) [decidable_pred (∈ e)] :
  ⁅e | h.to_fun i t⁆ = fintype.card e / fintype.card (sub_spec.range i) :=
((h.to_fun_equiv i t).prob_event_eq e).trans (prob_event_query_eq_div i t e)

end is_sub_spec

end oracle_spec

namespace oracle_comp

open oracle_spec sim_oracle

/-- Given a `is_sub_spec` instance between `sub_spec` and `super_spec`, we can coerce a computation
with oracles `sub_spec` to one with `super_spec` by simulating with `is_sub_spec.to_fun`. -/
instance coe_sub_spec (sub_spec super_spec : oracle_spec)
  [h : sub_spec ⊂ₒ super_spec] (α : Type) :
  has_coe (oracle_comp sub_spec α) (oracle_comp super_spec α) :=
{coe := λ oa, simulate' ⟪λ i t, h.to_fun i t⟫ oa ()}

lemma coe_sub_spec_def {sub_spec super_spec : oracle_spec} [h : sub_spec ⊂ₒ super_spec]
  (oa : oracle_comp sub_spec α) : (↑oa : oracle_comp super_spec α) =
    simulate' ⟪λ i t, h.to_fun i t⟫ oa () := rfl

section coe_sub_spec

variables (sub_spec super_spec : oracle_spec) [h : sub_spec ⊂ₒ super_spec]
  (a : α) (oa : oracle_comp sub_spec α) (ob : α → oracle_comp sub_spec β)
  (i : sub_spec.ι) (t : sub_spec.domain i) (f : α → β) (x : α) (e : set α)

include h

@[simp] lemma coe_sub_spec_return :
  (↑(return a : oracle_comp sub_spec α) : oracle_comp super_spec α) = return a := rfl

@[simp] lemma coe_sub_spec_bind :
  (↑(oa >>= ob) : oracle_comp super_spec β) = ↑oa >>= λ x, ↑(ob x) :=
begin
  simp_rw [coe_sub_spec_def, simulate'_bind, simulate'],
  simp only [map_eq_bind_pure_comp, bind_assoc, oracle_comp.pure_eq_return, pure_bind],
  refine congr_arg _ (funext (λ x, _)),
  rw [punit_eq x.2 ()],
end

@[simp] lemma coe_sub_spec_query :
  (↑(query i t) : oracle_comp super_spec (sub_spec.range i)) = h.to_fun i t :=
by simp only [coe_sub_spec_def, simulate'_query,
  stateless_oracle.apply_eq, map_bind, map_pure, bind_pure]

/-- Coercing a computation via a sub-spec instance doesn't change the associated distribution. -/
@[pairwise_dist_equiv] lemma coe_sub_spec_dist_equiv : (↑oa : oracle_comp super_spec α) ≃ₚ oa :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  { simp [coe_sub_spec_return] },
  {
    rw [coe_sub_spec_bind],
    refine bind_dist_equiv_bind_of_dist_equiv hoa (λ x _, hob x)
  },
  {
    rw [coe_sub_spec_query],
    exact h.to_fun_equiv i t
  }
end

@[pairwise_dist_equiv] lemma coe_sub_spec_bind_dist_equiv :
  (↑(oa >>= ob) : oracle_comp super_spec β) ≃ₚ
    (↑oa : oracle_comp super_spec α) >>= (λ x, ↑(ob x)) :=
begin
  rw_dist_equiv [coe_sub_spec_dist_equiv],
  refine bind_dist_equiv_bind_of_dist_equiv _ (λ _ _, _);
  rw_dist_equiv [coe_sub_spec_dist_equiv],
end

@[pairwise_dist_equiv] lemma coe_sub_spec_map_dist_equiv :
  (↑(f <$> oa) : oracle_comp super_spec β) ≃ₚ f <$> (↑oa : oracle_comp super_spec α) :=
by rw_dist_equiv [coe_sub_spec_bind_dist_equiv]

@[simp] lemma map_coe_sub_spec_dist_equiv_iff (ob : oracle_comp super_spec β) :
  f <$> (↑oa : oracle_comp super_spec α) ≃ₚ ob ↔ f <$> oa ≃ₚ ob :=
⟨dist_equiv.trans (map_dist_equiv_of_dist_equiv (λ _ _, rfl) (by pairwise_dist_equiv)),
  dist_equiv.trans (map_dist_equiv_of_dist_equiv (λ _ _, rfl) (by pairwise_dist_equiv))⟩

@[pairwise_dist_equiv] lemma coe_sub_spec_seq_dist_equiv (og : oracle_comp sub_spec (α → β)) :
  (↑(og <*> oa) : oracle_comp super_spec β) ≃ₚ
    (↑og : oracle_comp super_spec (α → β)) <*> ↑oa :=
begin
  rw_dist_equiv [coe_sub_spec_bind_dist_equiv],
  pairwise_dist_equiv_deep,
end

/-- `support` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma support_coe_sub_spec : (↑oa : oracle_comp super_spec α).support = oa.support :=
(coe_sub_spec_dist_equiv sub_spec super_spec oa).support_eq

/-- `fin_support` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma fin_support_coe_sub_spec [decidable_eq α] :
  (↑oa : oracle_comp super_spec α).fin_support = oa.fin_support :=
(coe_sub_spec_dist_equiv sub_spec super_spec oa).fin_support_eq

/-- `eval_dist` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma eval_dist_coe_sub_spec : ⁅(↑oa : oracle_comp super_spec α)⁆ = ⁅oa⁆ :=
(coe_sub_spec_dist_equiv sub_spec super_spec oa).eval_dist_eq

/-- `prob_output` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma prob_output_coe_sub_spec : ⁅= x | (↑oa : oracle_comp super_spec α)⁆ = ⁅= x | oa⁆ :=
(coe_sub_spec_dist_equiv sub_spec super_spec oa).prob_output_eq x

/-- `prob_event` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma prob_event_coe_sub_spec : ⁅e | (↑oa : oracle_comp super_spec α)⁆ = ⁅e | oa⁆ :=
(coe_sub_spec_dist_equiv sub_spec super_spec oa).prob_event_eq e

end coe_sub_spec

section simulate_coe_sub_spec

variables {sub_spec super_spec spec : oracle_spec} [h : sub_spec ⊂ₒ super_spec] {S S' : Type}
  (so : sim_oracle sub_spec spec S) (so' : sim_oracle super_spec spec S')
  (s : S) (s' : S') (a : α) (oa : oracle_comp sub_spec α) (ob : α → oracle_comp sub_spec β)
  (i : sub_spec.ι) (t : sub_spec.domain i)
include h

section support

@[simp] lemma support_simulate_coe_sub_spec_return :
  (simulate so' (return a : oracle_comp sub_spec α) s').support = {(a, s')} :=
begin
  rw [coe_sub_spec_return, simulate_return, support_return],
end
-- by rw [coe_sub_spec_return, simulate_map, simulate_return, support_map, support_return,
--   set.image_singleton, prod.map, id.def]

@[simp] lemma support_simulate'_coe_sub_spec_return :
  (simulate' so' (return a : oracle_comp sub_spec α) s').support = {a} :=
by simp only [support_simulate', support_simulate_coe_sub_spec_return, set.image_singleton]

@[simp] lemma support_simulate_coe_sub_spec_bind :
  (simulate so' (↑(oa >>= ob) : oracle_comp super_spec β) s').support =
    ⋃ x ∈ (simulate so' (↑oa : oracle_comp super_spec α) s').support,
      (simulate so' ↑(ob $ prod.fst x) x.2).support :=
by simp [coe_sub_spec_bind]
-- calc (simulate so' (↑(oa >>= ob) : oracle_comp super_spec β) s').support =
--   (simulate so' ↑oa s' >>= λ (x : α × S'), simulate so' ↑(ob x.1) x.2).support :
--     by simp_rw [coe_sub_spec_def, dsimulate', simulate', simulate_bind,
--       support_simulate_map_bind, simulate_map, support_bind_map, support_map,
--       simulate_eq_dsimulate, prod.map_snd, prod.map_fst, id.def]
--   ... = ⋃ x ∈ (simulate so' (↑oa : oracle_comp super_spec α) s').support,
--     (simulate so' ↑(ob $ prod.fst x) x.2).support : by rw [support_bind]

@[simp] lemma support_simulate'_coe_sub_spec_bind :
  (simulate' so' (↑(oa >>= ob) : oracle_comp super_spec β) s').support =
    ⋃ x ∈ (simulate so' (↑oa : oracle_comp super_spec α) s').support,
      (simulate' so' ↑(ob $ prod.fst x) x.2).support :=
by simp only [support_simulate', support_simulate_coe_sub_spec_bind, set.image_Union]

@[simp] lemma support_simulate_coe_sub_spec_query :
  (simulate so' (↑(query i t) : oracle_comp super_spec (sub_spec.range i)) s').support =
    (simulate so' (h.to_fun i t) s').support :=
by rw [coe_sub_spec_query]
-- by simp_rw [coe_sub_spec_def, dsimulate', simulate'_query, stateless_oracle.apply_eq,
--   support_simulate_map, support_simulate_bind, support_simulate_return, set.image_Union,
--   set.image_singleton, prod.map_mk, id.def, prod.mk.eta, set.bUnion_of_singleton]

/-- Given two simulation oracles `so : sim_oracle spec spec'' S` and
`so' : sim_oracle spec' spec'' : S'` with the starting specs satisfying `spec ⊂ₒ spec'`,
and a function `f : S → S'` between their states, if the support after simulating the
sub-spec coersion function with the second oracle looks like the support after simulating with the
first oracle then applying `f`, then simulating the coercion of any computation with the second
oracle has the same support as simulating the uncoerced computation and mapping by `f`. -/
lemma support_simulate_coe_sub_spec (f : S → S') (hf : ∀ i t s,
  (simulate so' (h.to_fun i t) (f s)).support = prod.map id f '' (so i (t, s)).support) :
  (simulate so' (↑oa : oracle_comp super_spec α) (f s)).support =
    (prod.map id f) '' (simulate so oa s).support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simpa only [support_simulate_coe_sub_spec_return,
      support_simulate_return, set.image_singleton] },
  { ext y,
    simp_rw [support_simulate_coe_sub_spec_bind, hoa, support_simulate_bind,
      set.image_Union, ← hob, set.mem_Union],
    refine ⟨λ h, let ⟨x, ⟨y', hy', hxy⟩, hx⟩ := h in ⟨y', hy', by simpa only [← hxy] using hx⟩,
      λ h, let ⟨x, hy, hx⟩ := h in ⟨(x.1, f x.2), ⟨x, hy, rfl⟩, hx⟩⟩ },
  { rw [support_simulate_coe_sub_spec_query, hf, support_simulate_query] }
end

/-- Version of `support_simulate_coe_sub_spec` for `simulate'`. In this case we get exact equality
between the support of the simulations, since the oracle states are irrelevent. -/
lemma support_simulate'_coe_sub_spec (f : S → S') (hf : ∀ i t s,
  (simulate so' (h.to_fun i t) (f s)).support = prod.map id f '' (so i (t, s)).support) :
  (simulate' so' (↑oa : oracle_comp super_spec α) (f s)).support = (simulate' so oa s).support :=
by simp only [support_simulate_coe_sub_spec so so' s oa f hf,
  set.image_image, support_simulate', prod_map, id.def]

end support

section fin_support



end fin_support

section eval_dist -- TODO: this all seems weird

@[simp] lemma eval_dist_simulate_coe_sub_spec_return :
  ⁅simulate so' ↑(return a : oracle_comp sub_spec α) s'⁆ = pmf.pure (a, s') :=
by simp only [coe_sub_spec_return, simulate_map, simulate_return, eval_dist_map, eval_dist_return,
  pmf.map_pure, prod.map_mk, id.def]

@[simp] lemma eval_dist_simulate_coe_sub_spec_bind :
  ⁅simulate so' (↑(oa >>= ob) : oracle_comp super_spec β) s'⁆ =
    ⁅simulate so' ↑oa s'⁆.bind (λ x, ⁅simulate so' ↑(ob $ prod.fst x) x.2⁆) :=
by simp [coe_sub_spec_bind]

/-- TOOD:stuff like this should use `dist_equiv` -/
@[simp] lemma eval_dist_simulate_coe_sub_spec_query :
  ⁅simulate so' (↑(query i t) : oracle_comp super_spec _) s'⁆ =
    ⁅simulate so' (h.to_fun i t) s'⁆ :=
by simp [coe_sub_spec_query]
-- by simp only [coe_sub_spec_query, eval_dist_simulate_map_bind, eval_dist_simulate_return,
--   pmf.map_pure, prod.map_mk, id.def, prod.mk.eta, pmf.bind_pure]

/-- Given two simulation oracles `so : sim_oracle spec spec'' S` and
`so' : sim_oracle spec' spec'' : S'` with the starting specs satisfying `spec ⊂ₒ spec'`,
and a function `f : S → S'` between their states, if the distribution after simulating the
sub-spec coersion function with the second oracle looks like the distribution after simulating with
the first oracle then applying `f`, then simulating the coercion of any computation with the second
oracle has the same distribution as simulating the uncoerced computation and mapping by `f`. -/
lemma eval_dist_simulate_coe_sub_spec (f : S → S') (hf : ∀ i t s,
  ⁅simulate so' (h.to_fun i t) (f s)⁆ = pmf.map (prod.map id f) ⁅so i (t, s)⁆) :
  ⁅simulate so' (↑oa : oracle_comp super_spec α) (f s)⁆ =
    ⁅simulate so oa s⁆.map (prod.map id f) :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simp only [eval_dist_simulate_coe_sub_spec_return, simulate_return, eval_dist_return,
      pmf.map_pure, prod.map_mk, id.def] },
  { simp_rw [eval_dist_simulate_coe_sub_spec_bind, hoa,
      eval_dist_simulate_bind, pmf.map_bind, pmf.bind_map],
    refine congr_arg (λ _, pmf.bind _ _) (funext $ λ x, (hob _ _)) },
  { rw [eval_dist_simulate_query, eval_dist_simulate_coe_sub_spec_query, hf] }
end

/-- Version of `eval_dist_simulate_coe_sub_spec` for `simulate'`. In this case we get exact
equality between the distributions of the simulations, since the oracle states are irrelevent. -/
lemma eval_dist_simulate'_coe_sub_spec (f : S → S') (hf : ∀ i t s,
  ⁅simulate so' (h.to_fun i t) (f s)⁆ = pmf.map (prod.map id f) ⁅so i (t, s)⁆) :
  ⁅simulate' so' (↑oa : oracle_comp super_spec α) (f s)⁆ = ⁅simulate' so oa s⁆ :=
by simp only [eval_dist_simulate', eval_dist_simulate_coe_sub_spec so so' s oa f hf, pmf.map_comp,
  prod.map_fst', function.comp.left_id]

end eval_dist

section prob_event

/-- Extension of `eval_dist_simulate_coe_sub_spec` to `prob_event`. We keep the same hypothesis
about `eval_dist` rather than a one in terms of `prob_event` for simplicity. -/
lemma prob_event_simulate_coe_sub_spec (e : set (α × S')) (f : S → S') (hf : ∀ i t s,
  ⁅simulate so' (h.to_fun i t) (f s)⁆ = pmf.map (prod.map id f) ⁅so i (t, s)⁆) :
  ⁅e | simulate so' (↑oa : oracle_comp super_spec α) (f s)⁆ =
    ⁅e | prod.map id f <$> simulate so oa s⁆ :=
by simp_rw [prob_event_eq_tsum_indicator, eval_dist_map,
  eval_dist_simulate_coe_sub_spec so so' s oa f hf]

/-- Extension of `eval_dist_simulate'_coe_sub_spec` to `prob_event`. We keep the same hypothesis
about `eval_dist` rather than a one in terms of `prob_event` for simplicity. -/
lemma prob_event_simulate'_coe_sub_spec (e : set α) (f : S → S') (hf : ∀ i t s,
  ⁅simulate so' (h.to_fun i t) (f s)⁆ = pmf.map (prod.map id f) ⁅so i (t, s)⁆) :
  ⁅e | simulate' so' (↑oa : oracle_comp super_spec α) (f s)⁆ = ⁅e | simulate' so oa s⁆ :=
by simpa only [prob_event_simulate', prob_event_simulate_coe_sub_spec so so' s oa _ f hf,
  prob_event_map, set.preimage_preimage, prod.map_fst]

end prob_event

end simulate_coe_sub_spec

end oracle_comp