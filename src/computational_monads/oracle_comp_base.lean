/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import computational_monads.oracle_spec
import probability.probability_mass_function.basic

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

/-- Simple computation flipping two coins and returning a value based on them -/
noncomputable example : oracle_comp coin_spec ℕ :=
do { b ← coin, b' ← coin,
  x ← return (if b && b' then 2 else 3),
  y ← return (if b || b' then 3 else 4),
  return (x * y) }

end query

end oracle_comp