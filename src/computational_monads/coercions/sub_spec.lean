/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.constructions.stateless_oracle
import computational_monads.constructions.uniform_select

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

/-- Relation defining an inclusion of one set of oracles into another, where the mapping
doesn't affect the underlying probability distribution of the computation. -/
class is_sub_spec (sub_spec super_spec : oracle_spec) :=
(to_fun (i : sub_spec.ι) (t : sub_spec.domain i) : oracle_comp super_spec (sub_spec.range i))
(eval_dist_to_fun' : ∀ i t, ⁅to_fun i t⁆ = ⁅query i t⁆)

infixl ` ⊂ₒ `:65 := is_sub_spec

namespace is_sub_spec

variables (sub_spec super_spec : oracle_spec) [h : sub_spec ⊂ₒ super_spec]
  (i : sub_spec.ι) (t : sub_spec.domain i)

@[simp] lemma support_to_fun : (h.to_fun i t).support = ⊤ :=
by rw [← support_eval_dist, h.eval_dist_to_fun', support_eval_dist, support_query]

@[simp] lemma fin_support_to_fun [∀ i t, (h.to_fun i t).decidable] :
  (h.to_fun i t).fin_support = ⊤ :=
by simp only [fin_support_eq_iff_support_eq_coe, finset.top_eq_univ,
  support_to_fun, set.top_eq_univ, finset.coe_univ]

@[simp] lemma eval_dist_to_fun : ⁅h.to_fun i t⁆ = pmf.uniform_of_fintype (sub_spec.range i) :=
by rw [h.eval_dist_to_fun', eval_dist_query]

@[simp] lemma prob_event_to_fun (e : set (sub_spec.range i)) :
  ⁅e | h.to_fun i t⁆ = ⁅e | query i t⁆ :=
prob_event_eq_of_eval_dist_eq (h.eval_dist_to_fun' i t) e

end is_sub_spec

end oracle_spec

namespace oracle_comp

open oracle_spec

/-- Given a `is_sub_spec` instance between `sub_spec` and `super_spec`, we can coerce a computation
with oracles `sub_spec` to one with `super_spec` by simulating with `is_sub_spec.to_fun`. -/
instance coe_sub_spec (sub_spec super_spec : oracle_spec) [h : sub_spec ⊂ₒ super_spec] (α : Type) :
  has_coe (oracle_comp sub_spec α) (oracle_comp super_spec α) :=
{coe := default_simulate' ⟪λ i t, h.to_fun i t⟫}

lemma coe_sub_spec_def {sub_spec super_spec : oracle_spec} [h : sub_spec ⊂ₒ super_spec]
  (oa : oracle_comp sub_spec α) : (↑oa : oracle_comp super_spec α) =
    default_simulate' ⟪λ i t, h.to_fun i t⟫ oa := rfl

section coe_sub_spec

variables (sub_spec super_spec : oracle_spec) [h : sub_spec ⊂ₒ super_spec]
  (a : α) (oa : oracle_comp sub_spec α) (ob : α → oracle_comp sub_spec β)
  (i : sub_spec.ι) (t : sub_spec.domain i)
include h

instance coe_sub_spec.decidable [∀ i t, (@is_sub_spec.to_fun sub_spec super_spec h i t).decidable]
  (oa : oracle_comp sub_spec α) [oa.decidable] : (↑oa : oracle_comp super_spec α).decidable :=
simulate'.decidable _ oa ()

lemma coe_sub_spec_return : (↑(return a : oracle_comp sub_spec α) : oracle_comp super_spec α) =
  prod.fst <$> return (a, ()) := rfl

lemma coe_sub_spec_bind : (↑(oa >>= ob) : oracle_comp super_spec β) =
  prod.fst <$> (default_simulate ⟪λ i t, h.to_fun i t⟫ oa >>=
    λ x, simulate ⟪λ i t, h.to_fun i t⟫ (ob x.1) x.2) :=
by rw [coe_sub_spec_def, default_simulate', simulate'_bind]

lemma coe_sub_spec_query : (↑(query i t) : oracle_comp super_spec (sub_spec.range i)) =
  prod.fst <$> (h.to_fun i t >>= λ u, return (u, ())) :=
by rw [coe_sub_spec_def, default_simulate', simulate'_query, stateless_oracle.apply_eq]

/-- `support` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma support_coe_sub_spec : (↑oa : oracle_comp super_spec α).support = oa.support :=
stateless_oracle.support_simulate'_eq_support _ _ ()
  (λ i t, is_sub_spec.support_to_fun sub_spec super_spec i t)

/-- `fin_support` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma fin_support_coe_sub_spec [∀ i t, (@is_sub_spec.to_fun sub_spec super_spec _ i t).decidable]
  [oa.decidable] : (↑oa : oracle_comp super_spec α).fin_support = oa.fin_support :=
by rw [fin_support_eq_fin_support_iff_support_eq_support, support_coe_sub_spec]

/-- `eval_dist` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma eval_dist_coe_sub_spec : ⁅(↑oa : oracle_comp super_spec α)⁆ = ⁅oa⁆ :=
stateless_oracle.eval_dist_simulate'_eq_eval_dist _ _ ()
  (λ i t, is_sub_spec.eval_dist_to_fun sub_spec super_spec i t)

/-- `prob_event` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma prob_event_coe_sub_spec (e : set α) : ⁅e | (↑oa : oracle_comp super_spec α)⁆ = ⁅e | oa⁆ :=
stateless_oracle.prob_event_simulate'_eq_prob_event _ _ ()
  (λ i t, is_sub_spec.eval_dist_to_fun sub_spec super_spec i t) e

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
by rw [coe_sub_spec_return, simulate_map, simulate_return, support_map, support_return,
  set.image_singleton, prod.map, id.def]

@[simp] lemma support_simulate'_coe_sub_spec_return :
  (simulate' so' (return a : oracle_comp sub_spec α) s').support = {a} :=
by simp only [support_simulate', support_simulate_coe_sub_spec_return, set.image_singleton]

@[simp] lemma support_simulate_coe_sub_spec_bind :
  (simulate so' (↑(oa >>= ob) : oracle_comp super_spec β) s').support =
    ⋃ x ∈ (simulate so' (↑oa : oracle_comp super_spec α) s').support,
      (simulate so' ↑(ob $ prod.fst x) x.2).support :=
calc (simulate so' (↑(oa >>= ob) : oracle_comp super_spec β) s').support =
  (simulate so' ↑oa s' >>= λ (x : α × S'), simulate so' ↑(ob x.1) x.2).support :
    by simp_rw [coe_sub_spec_def, default_simulate', simulate', simulate_bind,
      support_simulate_map_bind, simulate_map, support_bind_map, support_map,
      simulate_eq_default_simulate, prod.map_snd, prod.map_fst, id.def]
  ... = ⋃ x ∈ (simulate so' (↑oa : oracle_comp super_spec α) s').support,
    (simulate so' ↑(ob $ prod.fst x) x.2).support : by rw [support_bind]

@[simp] lemma support_simulate'_coe_sub_spec_bind :
  (simulate' so' (↑(oa >>= ob) : oracle_comp super_spec β) s').support =
    ⋃ x ∈ (simulate so' (↑oa : oracle_comp super_spec α) s').support,
      (simulate' so' ↑(ob $ prod.fst x) x.2).support :=
by simp only [support_simulate', support_simulate_coe_sub_spec_bind, set.image_Union]

@[simp] lemma support_simulate_coe_sub_spec_query :
  (simulate so' (↑(query i t) : oracle_comp super_spec (sub_spec.range i)) s').support =
    (simulate so' (h.to_fun i t) s').support :=
by simp_rw [coe_sub_spec_def, default_simulate', simulate'_query, stateless_oracle.apply_eq,
  support_simulate_map, support_simulate_bind, support_simulate_return, set.image_Union,
  set.image_singleton, prod.map_mk, id.def, prod.mk.eta, set.bUnion_of_singleton]

/-- Given two simulation oracles `so : sim_oracle spec spec'' S` and
`so' : sim_oracle spec' spec'' : S'` with the starting specs satisfying `spec ⊂ₒ spec'`,
and a function `f : S → S'` between their states, if the support after simulating the
sub-spec coersion function with the second oracle looks like the support after simulating with the
first oracle then applying `f`, then simulating the coercion of any computation with the second
oracle has the same support as simulating the uncoerced computation and mapping by `f`. -/
lemma support_simulate_coe_sub_spec (f : S → S')
  (hf : ∀ i t s, (simulate so' (h.to_fun i t) (f s)).support =
    prod.map id f '' (so i (t, s)).support) :
  (simulate so' (↑oa : oracle_comp super_spec α) (f s)).support =
    (prod.map id f) '' (simulate so oa s).support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  { simpa only [support_simulate_coe_sub_spec_return,
      support_simulate_return, set.image_singleton] },
  { simp_rw [support_simulate_coe_sub_spec_bind, hoa, support_simulate_bind,
      set.image_Union, ← hob],
    ext y,
    simp_rw [set.mem_Union],
    refine ⟨λ h, let ⟨x, ⟨y', hy', hxy⟩, hx⟩ := h in ⟨y', hy', by simpa only [← hxy] using hx⟩,
      λ h, let ⟨x, hy, hx⟩ := h in ⟨(x.1, f x.2), ⟨x, hy, rfl⟩, hx⟩⟩ },
  { rw [support_simulate_coe_sub_spec_query, hf, support_simulate_query] }
end

/-- Version of `support_simulate_coe_sub_spec` for `simulate'`. In this case we get exact equality
between the support of the simulations, since the oracle states are irrelevent. -/
lemma support_simulate'_coe_sub_spec (f : S → S')
  (hf : ∀ i t s, (simulate so' (h.to_fun i t) (f s)).support =
    prod.map id f '' (so i (t, s)).support) :
  (simulate' so' (↑oa : oracle_comp super_spec α) (f s)).support =
    (simulate' so oa s).support :=
by simp only [support_simulate_coe_sub_spec so so' s oa f hf,
  set.image_image, support_simulate', prod_map, id.def]

end support

section eval_dist

@[simp] lemma eval_dist_simulate_coe_sub_spec_return :
  ⁅simulate so' ↑(return a : oracle_comp sub_spec α) s'⁆ = pmf.pure (a, s') :=
by simp only [coe_sub_spec_return, simulate_map, simulate_return, eval_dist_map, eval_dist_return,
  pmf.map_pure, prod.map_mk, id.def]

@[simp] lemma eval_dist_simulate_coe_sub_spec_bind :
  ⁅simulate so' (↑(oa >>= ob) : oracle_comp super_spec β) s'⁆ =
    ⁅simulate so' ↑oa s'⁆.bind (λ x, ⁅simulate so' ↑(ob $ prod.fst x) x.2⁆) :=
calc ⁅simulate so' (↑(oa >>= ob) : oracle_comp super_spec β) s'⁆
  = ⁅simulate so' (default_simulate ⟪h.to_fun⟫ oa) s'⁆.bind (λ (x : (α × unit) × S'),
      ⁅simulate so' (simulate ⟪h.to_fun⟫ (ob x.1.1) x.1.2) x.2⁆.map (prod.map prod.fst id)) :
    begin
      simp only [coe_sub_spec_bind, simulate_map, simulate_bind, eval_dist_map, eval_dist_bind, pmf.map_bind],
    end
   ... = (⁅simulate so' (default_simulate ⟪h.to_fun⟫ oa) s'⁆.map (prod.map prod.fst id)).bind
      (λ (x : α × S'), ⁅simulate so' (default_simulate ⟪h.to_fun⟫ (ob x.1)) x.2⁆.map (prod.map prod.fst id)) :
    begin
      rw [pmf.bind_map],
      refine congr_arg (λ _, pmf.bind _ _) (funext $ λ x, _),
      simp only [function.comp_app, prod_map, id.def, stateless_oracle.simulate_eq_default_simulate],
    end
  ... = ⁅simulate so' (default_simulate' ⟪h.to_fun⟫ oa) s'⁆.bind (λ (x : α × S'),
      ⁅simulate so' (default_simulate ⟪h.to_fun⟫ (ob x.1)) x.2⁆.map (prod.map prod.fst id)) :
    begin
      rw [default_simulate', simulate', eval_dist_simulate_map],
    end
  ... = ⁅simulate so' ↑oa s'⁆.bind (λ (x : α × S'), ⁅simulate so' ↑(ob $ prod.fst x) x.2⁆) :
    begin
      simp [coe_sub_spec_def],
      refine congr_arg (λ _, pmf.bind _ _) (funext $ λ x, _),
      rw [simulate', eval_dist_simulate_map],
    end

@[simp] lemma eval_dist_simulate_coe_sub_spec_query :
  ⁅simulate so' (↑(query i t) : oracle_comp super_spec _) s'⁆ =
    ⁅simulate so' (h.to_fun i t) s'⁆ :=
by simp only [coe_sub_spec_query, eval_dist_simulate_map_bind, eval_dist_simulate_return,
  pmf.map_pure, prod.map_mk, id.def, prod.mk.eta, pmf.bind_pure]

/-- Given two simulation oracles `so : sim_oracle spec spec'' S` and
`so' : sim_oracle spec' spec'' : S'` with the starting specs satisfying `spec ⊂ₒ spec'`,
and a function `f : S → S'` between their states, if the distribution after simulating the
sub-spec coersion function with the second oracle looks like the distribution after simulating with
the first oracle then applying `f`, then simulating the coercion of any computation with the second
oracle has the same distribution as simulating the uncoerced computation and mapping by `f`. -/
lemma eval_dist_simulate_coe_sub_spec (f : S → S')
  (hf : ∀ i t s, ⁅simulate so' (h.to_fun i t) (f s)⁆ = pmf.map (prod.map id f) ⁅so i (t, s)⁆) :
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
lemma eval_dist_simulate'_coe_sub_spec (f : S → S')
  (hf : ∀ i t s, ⁅simulate so' (h.to_fun i t) (f s)⁆ = pmf.map (prod.map id f) ⁅so i (t, s)⁆) :
  ⁅simulate' so' (↑oa : oracle_comp super_spec α) (f s)⁆ = ⁅simulate' so oa s⁆ :=
by simp only [eval_dist_simulate', eval_dist_simulate_coe_sub_spec so so' s oa f hf, pmf.map_comp,
  prod.map_fst', function.comp.left_id]

end eval_dist


end simulate_coe_sub_spec

end oracle_comp