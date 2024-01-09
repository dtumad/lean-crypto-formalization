/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec
import control.monad.basic

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

/-- Representation of computations with oracle access.
`oracle_comp spec α` is a computation returning a value of type `α`,
potentially calling oracles given by `spec : oracle_spec`. -/
inductive oracle_comp (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp α
| query_bind' (i : spec.ι) (t : spec.domain i) (α : Type)
    (oa : spec.range i → oracle_comp α) : oracle_comp α

namespace oracle_comp

open oracle_spec

variables {spec : oracle_spec} {α β γ : Type}

/-- The eventual return type of a computation is never empty,
since it must eventually terminate by returning a value.
Uses the fact that the range of all oracles is inhabited in order
to explicitly choose a path to take at every bind.
Equivalently this is the final result if each oracle returns `default : spec.range i` -/
def default_result : Π {α : Type}, oracle_comp spec α → α
| _ (pure' α a) := a
| _ (query_bind' i t α oa) := default_result (oa default)

instance nonempty (spec : oracle_spec) (α : Type) [h : nonempty α] :
  nonempty (oracle_comp spec α) := h.elim (λ x, ⟨pure' α x⟩)

instance inhabited (spec : oracle_spec) (α : Type) [h : inhabited α] :
  inhabited (oracle_comp spec α) := ⟨pure' α default⟩

instance is_empty (spec : oracle_spec) (α : Type) [h : is_empty α] :
  is_empty (oracle_comp spec α) := ⟨λ oa, h.1 (default_result oa)⟩

/-- Constructing an `oracle_comp` implies the existence of some element of the underlying type.
  The assumption that the range of the oracles is `inhabited` is the key point for this. -/
def base_inhabited (oa : oracle_comp spec α) : inhabited α := ⟨oa.default_result⟩

/-- We define a monadic bind operation on `oracle_comp` by induction on the first computation.
With this definition `oracle_comp` satisfies the monad laws (see `oracle_comp.is_lawful_monad`). -/
def bind' : Π (α β : Type), oracle_comp spec α → (α → oracle_comp spec β) → oracle_comp spec β
| _ β (pure' α a) ob := ob a
| _ β (query_bind' i t α oa) ob := query_bind' i t β (λ u, bind' α β (oa u) ob)

section monad

instance (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := pure', bind := bind' }

protected lemma pure_def (spec : oracle_spec) {α : Type} (a : α) :
  (pure a : oracle_comp spec α) = pure' α a := rfl

protected lemma bind_def {spec : oracle_spec} {α β : Type}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  oa >>= ob = bind' α β oa ob := rfl

instance is_lawful_monad (spec : oracle_spec) :
  is_lawful_monad (oracle_comp spec) :=
{ pure_bind := λ α β a oa, rfl,
  id_map := λ α oa,
    begin
      induction oa with α a i t α oa hoa,
      { refl },
      { exact congr_arg (query_bind' i t α) (funext (λ u, hoa u)) }
    end,
  bind_assoc := λ α β γ oa ob oc,
    begin
      induction oa with α a i t α oa hoa,
      { refl },
      { exact congr_arg (query_bind' i t γ) (funext (λ u, hoa u ob)) }
    end,
  map_pure := λ α β f a, rfl,
  pure_seq_eq_map := λ α β g oa, rfl }

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

protected lemma return_bind (a : α) (ob : α → oracle_comp spec β) :
  return a >>= ob = ob a := pure_bind a ob

protected lemma bind_return (oa : oracle_comp spec α) : oa >>= return = oa := bind_pure oa

@[simp] lemma bind_query_bind' (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (query_bind' i t α oa) >>= ob = query_bind' i t β (λ u, oa u >>= ob) := rfl

@[simp] lemma map_map_eq_map_comp (oa : oracle_comp spec α) (f : α → β) (g : β → γ) :
  g <$> (f <$> oa) = (g ∘ f) <$> oa :=
by simp [oracle_comp.map_eq_bind_return_comp, bind_assoc]

lemma map_return (f : α → β) (a : α) : f <$> (return a : oracle_comp spec α) = return (f a) := rfl

protected lemma bind_congr {oa oa' : oracle_comp spec α} {ob ob' : α → oracle_comp spec β}
  (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' :=
h ▸ (congr_arg (λ ob, oa >>= ob) (funext h'))

lemma ite_bind (p : Prop) [decidable p] (oa oa' : oracle_comp spec α)
  (ob : α → oracle_comp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
by split_ifs; refl

lemma bind_seq (oa : oracle_comp spec α) (og : oracle_comp spec (α → β))
  (oc : β → oracle_comp spec γ) : (og <*> oa) >>= oc = og >>= λ f, oa >>= (oc ∘ f) :=
by simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

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
  rw [query_def, oracle_comp.bind_def],
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

/-- Shorthand for querying the right side of two available oracles.
TODO: remove -/
@[inline, reducible] def query₂ {spec spec' : oracle_spec}
  (i : spec'.ι) (t : spec'.domain i) : oracle_comp (spec ++ spec') (spec'.range i) :=
@query (spec ++ spec') (sum.inr i) t

/-- Simple computation flipping two coins and returning a value based on them -/
example : oracle_comp coin_spec ℕ :=
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

section no_confusion

@[simp] protected lemma pure'_ne_query_bind' (a : α) (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α) : pure' α a ≠ query_bind' i t α oa :=
λ h, oracle_comp.no_confusion h

@[simp] protected lemma query_bind'_ne_pure' (a : α) (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α) : query_bind' i t α oa ≠ pure' α a :=
λ h, oracle_comp.no_confusion h

@[simp] protected lemma return_eq_return_iff (a a' : α) :
  (return a : oracle_comp spec α) = return a' ↔ a = a' :=
⟨oracle_comp.pure'.inj, λ h, h ▸ rfl⟩

@[simp] protected lemma query_eq_query_iff (i : spec.ι) (t t' : spec.domain i) :
  query i t = query i t' ↔ t = t' :=
⟨λ h, eq_of_heq (oracle_comp.query_bind'.inj h).2.1, λ h, h ▸ rfl⟩

@[simp] protected lemma return_eq_bind_iff (b : β) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) : return b = oa >>= ob ↔ ∃ a, oa = return a ∧ ob a = return b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { cases oa with α a i t α oa,
    { exact ⟨a, rfl, symm h⟩ },
    { exact false.elim (oracle_comp.no_confusion h) } },
  { obtain ⟨a, ha⟩ := h,
    rw [ha.1, oracle_comp.return_bind, ha.2] }
end

@[simp] protected lemma bind_eq_return_iff (b : β) (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) : oa >>= ob = return b ↔ ∃ a, oa = return a ∧ ob a = return b :=
eq_comm.trans (oracle_comp.return_eq_bind_iff b oa ob)

@[simp] protected lemma query_ne_return (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  query i t ≠ return u := λ h, oracle_comp.no_confusion h

@[simp] protected lemma return_ne_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  return u ≠ query i t := λ h, oracle_comp.no_confusion h

protected lemma bind_eq_bind_iff (oa : oracle_comp spec α) (ob : oracle_comp spec β)
  (oc : α → oracle_comp spec γ) (oc' : β → oracle_comp spec γ) : oa >>= oc = ob >>= oc' ↔
  ((∃ a, oa = return a ∧ oc a = ob >>= oc') ∨ (∃ b, ob = return b ∧ oa >>= oc = oc' b) ∨
    (∃ (i : spec.ι) (t : spec.domain i) (oa' : spec.range i → oracle_comp spec α)
      (ob' : spec.range i → oracle_comp spec β), oa = query_bind' i t α oa' ∧
        ob = query_bind' i t β ob' ∧ (∀ u, oa' u >>= oc = ob' u >>= oc'))) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { cases oa with α a i t α oa,
    { exact or.inl ⟨a, rfl, h⟩ },
    { cases ob with β b i' t' β ob,
      { exact or.inr (or.inl ⟨b, rfl, h⟩) },
      { simp_rw [← oracle_comp.bind'_eq_bind, bind'] at h,
        obtain ⟨rfl, rfl, h⟩ := h,
        refine or.inr (or.inr ⟨i, t, oa, ob, ⟨rfl, rfl, λ u, _⟩⟩),
        convert function.funext_iff.1 (eq_of_heq h) u } } },
  { rcases h with ⟨a, ha, ha'⟩ | ⟨b, hb, hb'⟩ | ⟨i, t, oa', ob', h1, h2, h3⟩,
    { exact ha.symm ▸ ha' },
    { exact hb.symm ▸ hb' },
    { simp_rw [h1, h2, bind_query_bind', eq_self_iff_true, heq_self_iff_true, true_and, h3] } }
end

end no_confusion

end oracle_comp