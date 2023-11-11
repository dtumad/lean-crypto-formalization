/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec

/-!
# Computations with Oracle Access

TODO: some of this is out of date with the new `query_bind'` setup.

This file defines a representation of a computation with access to a set of oracles,
given by some `oracle_spec`. `oracle_comp spec α` will represent a computation
using the oracles of `spec : oracle_spec`, returning values of type `α`.
The definion is similar to a free monad, having built in `bind` and `pure` operations,
and an additional constructor for oracle queries.

We give probability distribution semantics for such a computation as `eval_dist` and `prob_event`.
`simulate` and `simulate'` will give semantics for running a computation by simulating the
oracles, using a (potentially empty) different set of oracles.

Notationally, we tend towards using `return` and `>>=` for the monadic operations,
and do-notation for specifying longer computations.

We additionally define a `decidable` typeclass for computations for which return values
all have `decidable_eq` instances, which will later be used to define `fin_support`.

Note that we don't have a constructor for unbounded recursion such as a fixpoint.
This creates issues with the distributional semantics since without termination it may not exist.
In theory this could be solved by introducing a typeclass for finite computation,
and only defining distributions on computations with such an instance.
However without a clear use case, we avoid doing this for simplicity.
-/

inductive oracle_comp (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp α
| query_bind' (i : spec.ι) (t : spec.domain i) (α : Type)
    (oa : spec.range i → oracle_comp α) : oracle_comp α

namespace oracle_comp

open oracle_spec

variables {spec : oracle_spec} {α β γ : Type}

instance nonempty (spec : oracle_spec) (α : Type) [h : nonempty α] :
  nonempty (oracle_comp spec α) := h.elim (λ x, ⟨pure' α x⟩)

instance inhabited (spec : oracle_spec) (α : Type) [h : inhabited α] :
  inhabited (oracle_comp spec α) := ⟨pure' α default⟩

/-- The eventual return type of a computation is never empty,
since it must eventually terminate by returning a value.
Uses the fact that the range of all oracles is inhabited in order
to explicitly choose a path to take at every bind.
Equivalently this is the final result if each oracle returns `default : spec.range i` -/
def default_result : Π {α : Type}, oracle_comp spec α → α
| _ (pure' α a) := a
| _ (query_bind' i t α oa) := default_result (oa default)

/-- Constructing an `oracle_comp` implies the existence of some element of the underlying type.
  The assumption that the range of the oracles is `inhabited` is the key point for this. -/
def base_inhabited (oa : oracle_comp spec α) : inhabited α := ⟨oa.default_result⟩

section bind

open_locale classical

noncomputable def bind' : Π (α β : Type), oracle_comp spec α →
  (α → oracle_comp spec β) → oracle_comp spec β
| _ β (pure' α a) ob := ob a
| _ β (query_bind' i t α oa) ob :=
  -- Check whether `ob` degenerates to `pure'`
  if h : α = β then if h.rec_on ob = pure' β
    then h.rec (query_bind' i t α oa) -- `h.rec` for typechecking
    else query_bind' i t β (λ u, bind' α β (oa u) ob)
    else query_bind' i t β (λ u, bind' α β (oa u) ob)

@[simp] lemma pure'_bind' (a : α) (ob : α → oracle_comp spec β) :
  bind' α β (pure' α a) ob = ob a := rfl

@[simp] lemma bind'_pure' (oa : oracle_comp spec α) :
  bind' α α oa (pure' α) = oa :=
by cases oa; simp only [bind', eq_self_iff_true, if_true, dite_eq_ite, heq_iff_eq, and_self]

lemma bind'_of_ne (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α)
  (ob : α → oracle_comp spec β) (h : α ≠ β) :
  bind' α β (query_bind' i t α oa) ob =
    query_bind' i t β (λ u, bind' α β (oa u) ob) :=
by simp only [bind', h, not_false_iff, dif_neg, eq_self_iff_true, heq_iff_eq, and_self]

lemma bind'_of_ne_pure' (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α)
  (ob : α → oracle_comp spec α) (h : ob ≠ pure' α) :
  bind' α α (query_bind' i t α oa) ob =
    query_bind' i t α (λ u, bind' α α (oa u) ob) :=
by simp only [bind', h, eq_self_iff_true, if_false, dite_eq_ite, if_true, heq_iff_eq, and_self]

@[simp] lemma bind'_eq_pure'_iff (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (y : β) :
  bind' α β oa ob = pure' β y ↔
    ∃ (x : α), oa = pure' α x ∧ ob x = pure' β y :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { induction oa with α a i t α oa hoa,
    { simpa using h },
    { by_cases hab : α = β,
      { induction hab,
        by_cases hb : ob = pure' α,
        { simpa [hb] using h },
        { simpa [bind'_of_ne_pure' _ _ _ _ hb] using h } },
      { simpa [bind'_of_ne _ _ _ _ hab] using h } } },
  { obtain ⟨x, hx, hy⟩ := h,
    simp [hx, hy] }
end

end bind

section monad

noncomputable instance (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := pure',
  bind := bind' }

lemma pure_def (spec : oracle_spec) {α : Type} (a : α) :
  (pure a : oracle_comp spec α) = pure' α a := rfl

lemma bind_def {spec : oracle_spec} {α β : Type}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  oa >>= ob = bind' α β oa ob := rfl

instance is_lawful_monad (spec : oracle_spec) :
  is_lawful_monad (oracle_comp spec) :=
{ pure_bind := λ α β a oa, rfl,
  id_map := λ α oa, bind'_pure' oa,
  bind_assoc := λ α β γ oa ob oc, begin
    simp only [bind_def],
    induction oa with α a i t α oa hoa,
    { refl },
    { by_cases hab : α = β,
      { induction hab,
        by_cases hb : ob = pure' α,
        { simp only [hb, bind'_pure', pure'_bind'] },
        { by_cases hac : α = γ,
          { induction hac,
            by_cases hc : oc = pure' α,
            { simp only [hc, bind'_pure', eq_self_iff_true, heq_iff_eq, and_self] },
            { simp [bind'_of_ne_pure' _ _ _ _ hc, bind'_of_ne_pure' _ _ _ _ hb, hoa],
              by_cases h' : (λ (x : α), bind' α α (ob x) oc) = pure' α,
              { simp only [h', bind'_pure', eq_self_iff_true, heq_iff_eq, and_self] },
              { simp only [bind'_of_ne_pure' _ _ _ _ h', eq_self_iff_true,
                  heq_iff_eq, and_self] } } },
          { simp only [bind'_of_ne _ _ _ _ hac, bind'_of_ne_pure' _ _ _ _ hb, hoa,
              eq_self_iff_true, heq_iff_eq, and_self] } } },
      { by_cases hbc : β = γ,
        { induction hbc,
          by_cases hc : oc = pure' β,
          { simp only [hc, bind'_of_ne _ _ _ _ hab, bind'_pure', eq_self_iff_true,
              heq_iff_eq, and_self] },
          { simp only [bind'_of_ne_pure' _ _ _ _ hc, bind'_of_ne _ _ _ _ hab, hoa,
              eq_self_iff_true, heq_iff_eq, and_self] } },
        { by_cases hac : α = γ,
          { induction hac,
            simp only [bind'_of_ne, hbc, hoa, hab, ne.def, not_false_iff],
            by_cases h' : (λ (x : α), bind' β α (ob x) oc) = pure' α,
            { simp only [h', bind'_pure', eq_self_iff_true, heq_iff_eq, and_self] },
            { simp only [bind'_of_ne_pure' _ _ _ _ h', eq_self_iff_true, heq_iff_eq, and_self] } },
          { simp only [bind'_of_ne, hbc, hac, hab, hoa, ne.def,
              not_false_iff, eq_self_iff_true, heq_iff_eq, and_self] } } } },
  end }


-- Notation for `return` with an explicit `spec` argument for convenience.
notation `return'` `!` spec `!` a := (return a : oracle_comp spec _)

@[simp] protected lemma pure'_eq_return (spec) :
  (pure' α : α → oracle_comp spec α) = return := funext (λ a, rfl)

@[simp] protected lemma pure_eq_return (spec) :
  (pure : α → oracle_comp spec α) = return := funext (λ a, rfl)

@[simp] protected lemma bind'_eq_bind (spec) :
  (bind' α β : oracle_comp spec α → (α → oracle_comp spec β) → oracle_comp spec β) = (>>=) := rfl

protected lemma bind_return_comp_eq_map (oa : oracle_comp spec α) (f : α → β) :
  oa >>= return ∘ f = f <$> oa := rfl

protected lemma map_eq_bind_return_comp (oa : oracle_comp spec α) (f : α → β) :
  f <$> oa = oa >>= return ∘ f := rfl

end monad

section query

/-- Shorthand for running a query and returning the value.
Generally this should be preferred over using `query_bind'` directly. -/
def query (i : spec.ι) (t : spec.domain i) : oracle_comp spec (spec.range i) :=
query_bind' i t (spec.range i) (pure' (spec.range i))

variables (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α)

lemma query_def : query i t = query_bind' i t (spec.range i) (pure' (spec.range i)) := rfl

@[simp] lemma query_bind'_eq_query_bind :
  query_bind' i t α oa = query i t >>= oa :=
begin
  rw [query_def, bind_def],
  by_cases ha : spec.range i = α,
  { induction ha,
    by_cases h : oa = pure' _; simp [bind', - oracle_comp.bind'_eq_bind,
      - oracle_comp.pure'_eq_return, h] },
  { simp [bind', ha] }
end

/-- Simple computation for qurying a coin-flipping oracle for a single result. -/
@[reducible, inline] def coin : oracle_comp coin_spec bool := query () ()

/-- Shorthand for querying the left side of two available oracles. -/
@[inline, reducible] def query₁ {spec spec' : oracle_spec}
  (i : spec.ι) (t : spec.domain i) : oracle_comp (spec ++ spec') (spec.range i) :=
@query (spec ++ spec') (sum.inl i) t

/-- Shorthand for querying the right side of two available oracles. -/
@[inline, reducible] def query₂ {spec spec' : oracle_spec}
  (i : spec'.ι) (t : spec'.domain i) : oracle_comp (spec ++ spec') (spec'.range i) :=
@query (spec ++ spec') (sum.inr i) t

/-- Simple computation flipping two coins and returning a value based on them -/
noncomputable example : oracle_comp coin_spec ℕ :=
do { b ← coin, b' ← coin,
  x ← return (if b && b' then 2 else 3),
  y ← return (if b || b' then 3 else 4),
  return (x * y) }

end query

/-- Slightly nicer induction priciple, avoiding use of `bind'` and `pure'`.
  Use as induction principle with `induction oa using oracle_comp.induction_on` -/
@[elab_as_eliminator] protected def induction_on
  {C : Π {α : Type}, oracle_comp spec α → Sort*}
  {α : Type} (oa : oracle_comp spec α)
  (h_return : ∀ {α : Type} (a : α), C (return a))
  (h_bind : ∀ {α β : Type} {oa : oracle_comp spec α} {ob : α → oracle_comp spec β},
    C oa → (∀ a, C (ob a)) → C (oa >>= ob) )
  (h_query : ∀ i t, C (query i t)) : C oa :=
begin
  induction oa with α a i t α oa hoa,
  { exact h_return a },
  { rw [query_bind'_eq_query_bind],
    exact h_bind (h_query i t) hoa }
end

@[elab_as_eliminator] protected def induction_on'
  {C : Π {α : Type}, oracle_comp spec α → Sort*}
  {α : Type} (oa : oracle_comp spec α)
  (h_return : ∀ {α : Type} (a : α), C (return a))
  (h_query_bind : ∀ (i : spec.ι) (t : spec.domain i) {α : Type}
    {oa : spec.range i → oracle_comp spec α},
    (∀ u, C (oa u)) → C (query i t >>= oa)) : C oa :=
begin
  induction oa with α a i t α oa hoa,
  { exact h_return a },
  { rw [query_bind'_eq_query_bind],
    exact h_query_bind i t hoa }
end

/-- Check that the induction principal works properly. -/
example (oa : oracle_comp spec α) : true :=
by induction oa using oracle_comp.induction_on; trivial

/-- Check that the induction principal works properly. -/
example (oa : oracle_comp spec α) : true :=
by induction oa using oracle_comp.induction_on'; trivial

section tactics

/-- Perform induction on the given computation, using `oracle_comp.induction_on` as the eliminator.
This has better naming conventions, and uses `return` and `>>=` over `pure'` and `bind'`. -/
protected meta def default_induction (h : interactive.parse lean.parser.ident) :
  tactic (list (name × list expr × list (name × expr))) :=
do { oa ← tactic.get_local h,
  tactic.induction oa [`α, `a, `α, `β, `oa, `ob, `hoa, `hob, `i, `t] `oracle_comp.induction_on }

/-- Perform induction on the given computation, using `oracle_comp.induction_on` as the eliminator.
This has better naming conventions, and uses `return` and `>>=` over `pure'` and `bind'`. -/
protected meta def default_induction' (h : interactive.parse lean.parser.ident) :
  tactic (list (name × list expr × list (name × expr))) :=
do { oa ← tactic.get_local h,
  tactic.induction oa [`α, `a, `i, `t, `α, `oa, `hoa] `oracle_comp.induction_on' }

end tactics

-- section no_confusion

-- variables (b : β) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
--   (i : spec.ι) (t : spec.domain i) (u : spec.range i)
--   (ou : α → oracle_comp spec (spec.range i))
--   (f : α → β) (g : α → spec.range i)

-- @[simp] lemma return_ne_bind : (return' !spec! b) ≠ oa >>= ob := λ h, oracle_comp.no_confusion h
-- @[simp] lemma bind_ne_return : oa >>= ob ≠ (return' !spec! b) := λ h, oracle_comp.no_confusion h
-- @[simp] lemma return_ne_query : (return' !spec! u) ≠ query i t := λ h, oracle_comp.no_confusion h
-- @[simp] lemma query_ne_return : query i t ≠ (return' !spec! u) := λ h, oracle_comp.no_confusion h
-- @[simp] lemma bind_ne_query : oa >>= ou ≠ query i t := λ h, oracle_comp.no_confusion h
-- @[simp] lemma query_ne_bind : query i t ≠ oa >>= ou := λ h, oracle_comp.no_confusion h

-- @[simp] lemma map_ne_return : (return' !spec! b) ≠ f <$> oa :=
-- by simp [oracle_comp.map_eq_bind_return_comp]
-- @[simp] lemma return_ne_map : f <$> oa ≠ (return' !spec! b) :=
-- by simp [oracle_comp.map_eq_bind_return_comp]

-- @[simp] lemma map_ne_query : g <$> oa ≠ query i t := by simp [oracle_comp.map_eq_bind_return_comp]
-- @[simp] lemma query_ne_map : query i t ≠ g <$> oa := by simp [oracle_comp.map_eq_bind_return_comp]

-- @[simp] lemma return_eq_return_iff (spec : oracle_spec) (a a' : α) :
--   (return' !spec! a) = (return' !spec! a') ↔ a = a' :=
-- ⟨λ h, oracle_comp.pure'.inj h, λ h, h ▸ rfl⟩

-- @[simp] lemma bind'_eq_bind'_iff (oa oa' : oracle_comp spec α) (ob ob' : α → oracle_comp spec β) :
--   oa >>= ob = oa' >>= ob' ↔ oa = oa' ∧ ob = ob' :=
-- ⟨λ h, let ⟨h, ha, hb⟩ := oracle_comp.bind'.inj h in
--   ⟨eq_of_heq ha, eq_of_heq hb⟩, λ h, by simp [h.1, h.2]⟩

-- @[simp] lemma query_eq_query_iff (i : spec.ι) (t t' : spec.domain i) :
--   query i t = query i t' ↔ t = t' := ⟨λ h, oracle_comp.query.inj h, λ h, h ▸ rfl⟩

-- end no_confusion

end oracle_comp