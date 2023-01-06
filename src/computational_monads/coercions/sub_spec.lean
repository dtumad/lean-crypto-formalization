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

open oracle_comp distribution_semantics

/-- Relation defining an inclusion of one set of oracles into another, where the mapping
doesn't affect the underlying probability distribution of the computation. -/
class is_sub_spec (spec spec' : oracle_spec) :=
(to_fun (i : spec.ι) : spec.domain i → oracle_comp spec' (spec.range i))
(eval_dist_to_fun' : ∀ i t, ⁅to_fun i t⁆ = ⁅query i t⁆)

infixl ` ⊂ₒ `:65 := is_sub_spec

namespace is_sub_spec

variables (spec spec' : oracle_spec) [h : spec ⊂ₒ spec']

@[simp] lemma support_to_fun  (i : spec.ι) (t : spec.domain i) : (h.to_fun i t).support = ⊤ :=
by rw [← support_eval_dist, h.eval_dist_to_fun', support_eval_dist, support_query]

@[simp] lemma fin_support_to_fun [∀ i t, (h.to_fun i t).decidable]
  (i : spec.ι) (t : spec.domain i) : (h.to_fun i t).fin_support = ⊤ :=
by simp only [fin_support_eq_iff_support_eq_coe, finset.top_eq_univ,
  support_to_fun, set.top_eq_univ, finset.coe_univ]

@[simp] lemma eval_dist_to_fun (i : spec.ι) (t : spec.domain i) :
  ⁅h.to_fun i t⁆ = pmf.uniform_of_fintype (spec.range i) :=
by rw [h.eval_dist_to_fun', eval_dist_query]

@[simp] lemma prob_event_to_fun (i : spec.ι) (t : spec.domain i) (e : set (spec.range i)) :
  ⁅e | h.to_fun i t⁆ = ⁅e | query i t⁆ :=
prob_event_eq_of_eval_dist_eq (h.eval_dist_to_fun' i t) e

end is_sub_spec

end oracle_spec

namespace oracle_comp

open oracle_spec distribution_semantics

/-- Given a `is_sub_spec` instance between `spec` and `sub_spec`, we can coerce a computation
with oracles `spec` to one with oracles `spec'` by simulating with the sub-spec function. -/
instance coe_sub_spec (spec spec' : oracle_spec) [h : spec ⊂ₒ spec'] (α : Type) :
  has_coe (oracle_comp spec α) (oracle_comp spec' α) :=
{coe := default_simulate' ⟪λ i t, h.to_fun i t⟫}

lemma coe_sub_spec_def {spec spec' : oracle_spec} [h : spec ⊂ₒ spec'] (oa : oracle_comp spec α) :
  (↑oa : oracle_comp spec' α) = default_simulate' ⟪λ i t, h.to_fun i t⟫ oa := rfl

variables (spec spec' spec'' : oracle_spec) [h : spec ⊂ₒ spec']
include h

instance coe_sub_spec.decidable [∀ i t, (@is_sub_spec.to_fun spec spec' _ i t).decidable]
  (oa : oracle_comp spec α) [oa.decidable] : (↑oa : oracle_comp spec' α).decidable :=
simulate'.decidable _ oa ()

lemma coe_sub_spec_return (a : α) :
  (↑(return a : oracle_comp spec α) : oracle_comp spec' α) = prod.fst <$> return (a, ()) := rfl

lemma coe_sub_spec_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (↑(oa >>= ob) : oracle_comp spec' β) =
    prod.fst <$> (default_simulate ⟪λ i t, h.to_fun i t⟫ oa >>=
      λ x, simulate ⟪λ i t, h.to_fun i t⟫ (ob x.1) x.2) :=
by rw [coe_sub_spec_def, default_simulate', simulate'_bind]

lemma coe_sub_spec_query (i : spec.ι) (t : spec.domain i) :
  (↑(query i t) : oracle_comp spec' (spec.range i)) =
    prod.fst <$> (h.to_fun i t >>= λ u, return (u, ())) :=
by rw [coe_sub_spec_def, default_simulate', simulate'_query, stateless_oracle.apply_eq]

/-- `support` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma support_coe_sub_spec (oa : oracle_comp spec α) :
  (↑oa : oracle_comp spec' α).support = oa.support :=
stateless_oracle.support_simulate'_eq_support _ _ ()
  (λ i t, is_sub_spec.support_to_fun spec spec' i t)

/-- `fin_support` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma fin_support_coe_sub_spec [∀ i t, (@is_sub_spec.to_fun spec spec' _ i t).decidable]
  (oa : oracle_comp spec α) [oa.decidable] :
  (↑oa : oracle_comp spec' α).fin_support = oa.fin_support :=
by rw [fin_support_eq_fin_support_iff_support_eq_support, support_coe_sub_spec]

/-- `eval_dist` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma eval_dist_coe_sub_spec (oa : oracle_comp spec α) :
  ⁅(↑oa : oracle_comp spec' α)⁆ = ⁅oa⁆ :=
stateless_oracle.eval_dist_simulate'_eq_eval_dist _ _ ()
  (λ i t, is_sub_spec.eval_dist_to_fun spec spec' i t)

/-- `prob_event` is unchanged after coercing a computation via a sub-spec instance. -/
@[simp] lemma prob_event_coe_sub_spec (oa : oracle_comp spec α) (e : set α) :
  ⁅e | (↑oa : oracle_comp spec' α)⁆ = ⁅e | oa⁆ :=
stateless_oracle.prob_event_simulate'_eq_prob_event _ _ ()
  (λ i t, is_sub_spec.eval_dist_to_fun spec spec' i t) e

section simulate

variables {S S' : Type} {spec''' : oracle_spec} (so : sim_oracle spec spec''' S) (so' : sim_oracle spec' spec'' S')
  (s : S) (f : S → S')

-- lemma support_simulate_coe_sub_spec_return (a : α)

@[simp] lemma support_simulate_coe_sub_spec_return (s' : S') (a : α) :
  (simulate so' (↑(return a : oracle_comp spec α) : oracle_comp spec' α) s').support = {(a, s')} :=
by rw [coe_sub_spec_return, simulate_map, simulate_return, support_map, support_return,
  set.image_singleton, prod.map, id.def]

@[simp] lemma support_simulate_coe_sub_spec_bind (s' : S') (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) :
    (simulate so' (↑(oa >>= ob) : oracle_comp spec' β) s').support =
      (simulate so' (↑oa : oracle_comp spec' α) s' >>=
        λ (x : α × S'), simulate so' ↑(ob x.1) x.2).support :=
begin
  simp_rw [coe_sub_spec_def, default_simulate', simulate', simulate_bind,
    support_simulate_map_bind, simulate_bind, simulate_map],
  rw [support_bind_map],
  congr,
  ext x,
  obtain ⟨⟨a, u⟩, s⟩ := x,
  induction u,
  rw [function.comp_app],
  refl,
end

-- set_option trace.class_instances

@[simp] lemma support_simulate_coe_sub_spec_query (s' : S') (i : spec.ι) (t : spec.domain i) :
  (simulate so' (↑(query i t) : oracle_comp spec' (spec.range i)) s').support =
    (simulate so' (h.to_fun i t) s').support :=
begin
  simp [coe_sub_spec_def, support_return],
  simp_rw [support_return],
  simp,
end

lemma support_simulate_coe_sub_spec (oa : oracle_comp spec α)
  (hf' : ∀ i t s, (simulate so' (h.to_fun i t) (f s)).support =
    prod.map id f '' (so i (t, s)).support)
   :
  ((simulate so' (↑oa : oracle_comp spec' α) (f s)).support : set (α × S')) =
    (prod.map id f) '' (simulate so oa s).support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t generalizing s,
  {
    rw [support_simulate_coe_sub_spec_return, simulate_return, support_return, set.image_singleton,
      prod_map, id.def],
  },
  {
    calc (simulate so' ↑(oa >>= ob) (f s)).support
      = (simulate so' ↑oa (f s) >>=
              λ (x : α × S'), simulate so' (↑(ob x.1)) x.2).support :
        support_simulate_coe_sub_spec_bind _ _ _ _ _ _ _
      ... = prod.map id f '' (simulate so oa s >>=
              λ (x : α × S), simulate so (ob x.1) x.2).support :
        begin
          simp_rw [support_bind, hoa],


          ext y,
          simp only [set.mem_image, set.mem_Union],
          refine ⟨λ h, _, λ h, _⟩,
          {
            obtain ⟨⟨a, s''⟩, ⟨m, hm⟩, hn⟩ := h,
            rw [prod.eq_iff_fst_eq_snd_eq] at hm,
            have : s'' = f m.2 := begin
              exact hm.2.2.symm,
            end,
            simp_rw [this, hob, set.mem_image] at hn,
            obtain ⟨b, hb, hb'⟩ := hn,
            refine ⟨b, ⟨m, hm.1, hm.2.1.symm ▸ hb⟩, hb'⟩,
          },
          {
            obtain ⟨x, ⟨z, hz, hzx⟩, hx'⟩ := h,
            refine ⟨prod.map id f z, ⟨z, hz, rfl⟩, _⟩,
            specialize hob z.1 z.2,
            simp_rw [prod_map, id.def, hob, ← hx', set.mem_image],
            refine ⟨x, hzx, rfl⟩,
          }

        end
      ... = ⋃ (x : α × S) (hx : x ∈ (simulate so oa s).support),
          prod.map id f '' (simulate so (ob x.1) x.2).support :
        by simp only [support_bind, set.image_Union]
      ... = prod.map id f '' (simulate so (oa >>= ob) s).support :
        by simp_rw [support_simulate_bind, set.image_Union]
  },
  {

    simp_rw [coe_sub_spec_query, simulate_map, support_map,
      simulate_bind, simulate_return, support_bind, support_return, set.image_Union],
    simp only [prod_map, id.def, set.image_singleton, prod.mk.eta, set.bUnion_of_singleton],
    exact hf' i t s,
  }
end

end simulate

end oracle_comp

namespace oracle_spec

open oracle_comp distribution_semantics

/-- coerce a coin flip into a uniform random selection of a `bool` -/
@[priority std.priority.default+100]
instance : is_sub_spec coin_spec uniform_selecting :=
{ to_fun := λ i t, $ᵛ (tt ::ᵥ ff ::ᵥ vector.nil),
  eval_dist_to_fun' := λ i t, pmf.ext (λ x, by cases x;
    simp_rw [eval_dist_uniform_select_vector_apply, vector.to_list_cons,
      vector.to_list_nil, list.count_cons, list.count_nil, eq_self_iff_true, if_true, if_false,
      eval_dist_query_apply, card_range_coin_spec, nat.cast_one]) }

/-- Coerce a computation to one with access to another oracle on the left,
forwarding the old queries to the left side of the combined set of oracles. -/
@[priority std.priority.default]
instance is_sub_spec_append_left (spec spec' : oracle_spec) : spec ⊂ₒ (spec' ++ spec) :=
{ to_fun := λ i t, @query (spec' ++ spec) (sum.inr i) t,
  eval_dist_to_fun' := λ i t, trans (eval_dist_query (sum.inr i) t) (eval_dist_query i t).symm }

/-- Coerce a computation to one with access to another oracle on the right,
forwarding the old queries to the left side of the combined set of oracles. -/
@[priority std.priority.default+1]
instance is_sub_spec_append_right (spec spec' : oracle_spec) : spec ⊂ₒ (spec ++ spec') :=
{ to_fun := λ i t, @query (spec ++ spec') (sum.inl i) t,
  eval_dist_to_fun' := λ i t, trans (eval_dist_query (sum.inl i) t) (eval_dist_query i t).symm }

lemma is_sub_spec_append_right_apply {spec spec' : oracle_spec} (i : spec.ι) (t : spec.domain i) :
  (oracle_spec.is_sub_spec_append_right spec spec').to_fun i t =
    @query (spec ++ spec') (sum.inl i) t := rfl

/-- Coerce an oracle and then append to the left. Already sort of exists,
  but the instance priorities don't work without explicitly having this. -/
@[priority std.priority.default+10]
instance is_sub_spec_append_left_of_is_sub_spec (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec sub_spec (spec ++ super_spec) :=
{ to_fun := λ i t, ↑(h.to_fun i t),
  eval_dist_to_fun' := λ i t,by rw [eval_dist_coe_sub_spec, is_sub_spec.eval_dist_to_fun'] }


/-- Coerce an oracle and then append to the right. Already sort of exists,
  but the instance priorities don't work without explicitly having this. -/
@[priority std.priority.default+11]
instance is_sub_spec_append_right_of_is_sub_spec (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec sub_spec (super_spec ++ spec) :=
{ to_fun := λ i t, ↑(h.to_fun i t),
  eval_dist_to_fun' := λ i t,by rw [eval_dist_coe_sub_spec, is_sub_spec.eval_dist_to_fun'] }

/-- Coerce the oracle on the right side of an existing set of appended oracles. -/
@[priority std.priority.default+20]
instance is_sub_spec_left_side_append (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec (sub_spec ++ spec) (super_spec ++ spec) :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, (append.range_inl sub_spec spec i).symm.rec (h.to_fun i t)
  | (sum.inr i) := λ t, @query (super_spec ++ _) (sum.inr i) t
  end,
  eval_dist_to_fun' := λ i, match i with
  | (sum.inl i) := λ t, (eval_dist_coe_sub_spec _ _ (h.to_fun i t)).trans
      ((h.eval_dist_to_fun' i t).trans rfl)
  | (sum.inr i) := λ t, rfl
  end }

/-- Coerce the oracle on the right side of an existing set of appended oracles. -/
@[priority std.priority.default+21]
instance is_sub_spec_right_side_append (spec sub_spec super_spec : oracle_spec)
  [h : is_sub_spec sub_spec super_spec] : is_sub_spec (spec ++ sub_spec) (spec ++ super_spec) :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, @query (_ ++ super_spec) (sum.inl i) t
  | (sum.inr i) := λ t, (append.range_inr spec sub_spec i).symm.rec (h.to_fun i t)
  end,
  eval_dist_to_fun' := λ i, match i with
  | (sum.inl i) := λ t, rfl
  | (sum.inr i) := λ t, (eval_dist_coe_sub_spec _ _ (h.to_fun i t)).trans
      ((h.eval_dist_to_fun' i t).trans rfl)
  end }

/-- Coerce towards a standardized append ordering (matching the `infixl` declaration for `++`) -/
@[priority std.priority.default+30]
instance is_sub_spec_assoc (spec spec' spec'' : oracle_spec) :
  is_sub_spec (spec ++ (spec' ++ spec'')) (spec ++ spec' ++ spec'') :=
{ to_fun := λ i, match i with
  | (sum.inl i) := λ t, @query (spec ++ spec' ++ spec'') (sum.inl (sum.inl i)) t
  | (sum.inr (sum.inl i)) := λ t, @query (spec ++ spec' ++ spec'') (sum.inl (sum.inr i)) t
  | (sum.inr (sum.inr i)) := λ t, @query (spec ++ spec' ++ spec'') (sum.inr i) t
  end,
  eval_dist_to_fun' := λ i, match i with
  | (sum.inl i) := λ t, rfl
  | (sum.inr (sum.inl i)) := λ t, rfl
  | (sum.inr (sum.inr i)) := λ t, rfl
  end }

end oracle_spec

namespace oracle_spec

open oracle_comp

section examples

-- This set of examples serves as sort of a "unit test" for the coercions above
variables (spec spec' spec'' spec''' : oracle_spec) (coe_spec coe_spec' : oracle_spec)
  [coe_spec ⊂ₒ coe_spec']

-- coerce a single `coin_spec` and then append extra oracles
example (oa : oracle_comp coe_spec α) :
  oracle_comp (coe_spec' ++ spec' ++ spec'') α := ↑oa
example (oa : oracle_comp coe_spec α) :
  oracle_comp (spec ++ coe_spec' ++ spec') α := ↑oa
example (oa : oracle_comp coe_spec α) :
  oracle_comp (spec ++ spec' ++ coe_spec') α := ↑oa

-- coerce left side of append and then append on additional oracles
example (oa : oracle_comp (coe_spec ++ spec) α) :
  oracle_comp (coe_spec' ++ spec ++ spec') α := ↑oa
example (oa : oracle_comp (coe_spec ++ spec) α) :
  oracle_comp (coe_spec' ++ spec' ++ spec) α := ↑oa
example (oa : oracle_comp (coe_spec ++ spec) α) :
  oracle_comp (spec' ++ coe_spec' ++ spec) α := ↑oa

-- coerce right side of append and then append on additional oracles
example (oa : oracle_comp (spec ++ coe_spec) α) :
  oracle_comp (spec ++ coe_spec' ++ spec') α := ↑oa
example (oa : oracle_comp (spec ++ coe_spec) α) :
  oracle_comp (spec ++ spec' ++ coe_spec') α := ↑oa
example (oa : oracle_comp (spec ++ coe_spec) α) :
  oracle_comp (spec' ++ spec ++ coe_spec') α := ↑oa

-- coerce an inside part while also applying associativity
example (oa : oracle_comp (spec ++ (spec' ++ coe_spec)) α) :
  oracle_comp (spec ++ spec' ++ coe_spec') α := ↑oa
example (oa : oracle_comp (spec ++ (coe_spec ++ spec')) α) :
  oracle_comp (spec ++ coe_spec' ++ spec') α := ↑oa
example (oa : oracle_comp (coe_spec ++ (spec ++ spec')) α) :
  oracle_comp (coe_spec' ++ spec ++ spec') α := ↑oa

-- coerce two oracles up to four oracles
example (oa : oracle_comp (spec ++ spec') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec ++ spec'') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec' ++ spec'') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec'' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa

-- coerce threee oracles up to four oracles
example (oa : oracle_comp (spec ++ spec' ++ spec'') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec ++ spec' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec ++ spec'' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp (spec' ++ spec'' ++ spec''') α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ spec''') α := ↑oa

-- four oracles with associativity and internal coercion
example (oa : oracle_comp ((coe_spec ++ spec') ++ (spec'' ++ spec''')) α) :
  oracle_comp (coe_spec' ++ spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp ((spec ++ spec') ++ (coe_spec ++ spec''')) α) :
  oracle_comp (spec ++ spec' ++ coe_spec' ++ spec''') α := ↑oa
example (oa : oracle_comp ((spec ++ coe_spec) ++ (spec'' ++ spec''')) α) :
  oracle_comp (spec ++ coe_spec' ++ spec'' ++ spec''') α := ↑oa
example (oa : oracle_comp ((spec ++ spec') ++ (spec'' ++ coe_spec')) α) :
  oracle_comp (spec ++ spec' ++ spec'' ++ coe_spec') α := ↑oa

/-- coercion makes it possible to mix computations on individual oracles -/
example {spec : oracle_spec} : oracle_comp (uniform_selecting ++ spec) bool :=
do { n ←$[0..10], b ← coin, if n ≤ 3 ∧ b = tt then return ff else coin }

end examples

end oracle_spec
