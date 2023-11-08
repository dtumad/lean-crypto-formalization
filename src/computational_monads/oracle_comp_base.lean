/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import computational_monads.oracle_spec
import probability.probability_mass_function.basic

universes u v

namespace double

inductive oracle_comp (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp α
| query_bind' (i : spec.ι) (t : spec.domain i) (α : Type)
    (oa : spec.range i → oracle_comp α) : oracle_comp α

open oracle_comp

def inhabited_base {spec : oracle_spec} : Π {α : Type},
  oracle_comp spec α → α
| _ (pure' α a) := a
| _ (query_bind' i t α oa) := inhabited_base (oa default)

/-- Shorthand for running a query and returning the value.
Generally this should be preferred over using `query_bind'` directly. -/
def query {spec : oracle_spec} (i : spec.ι) (t : spec.domain i) :
  oracle_comp spec (spec.range i) :=
query_bind' i t (spec.range i) (pure' (spec.range i))

section bind

open_locale classical

noncomputable def bind' {spec : oracle_spec} : Π (α β : Type),
  oracle_comp spec α → (α → oracle_comp spec β) →
    oracle_comp spec β
| _ β (pure' α a) ob := ob a
| _ β (query_bind' i t α oa) ob :=
  -- Check whether `ob` degenerates to `pure'`
  if h : α = β then if h.rec_on ob = pure' β
    then h.rec (query_bind' i t α oa) -- `h.rec` for typechecking
    else query_bind' i t β (λ u, bind' α β (oa u) ob)
    else query_bind' i t β (λ u, bind' α β (oa u) ob)

variables {spec : oracle_spec} {α β : Type}

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
  {
    induction oa with α a i t α oa hoa,
    {
      simpa using h,
    },
    {
      by_cases hab : α = β,
      {
        induction hab,
        by_cases hb : ob = pure' α,
        {
          simpa [hb] using h,
        },
        {
          simpa [bind'_of_ne_pure' _ _ _ _ hb] using h,
        }
      },
      {
        simpa [bind'_of_ne _ _ _ _ hab] using h,
      }

    }
  },
  {
    obtain ⟨x, hx, hy⟩ := h,
    simp [hx, hy],
  }
end

end bind

noncomputable instance (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := pure',
  bind := bind' }

lemma pure_eq_pure' (spec : oracle_spec) {α : Type} (a : α) :
  (pure a : oracle_comp spec α) = pure' α a := rfl

lemma bind_eq_bind' (spec : oracle_spec) {α β : Type}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  oa >>= ob = bind' α β oa ob := rfl

instance is_lawful_monad (spec : oracle_spec) :
  is_lawful_monad (oracle_comp spec) :=
{ pure_bind := begin
    intros,
    refl,
  end,
  id_map := begin
    intros α oa,
    show bind' α α oa (λ x, pure' α x) = oa,
    induction oa with α a i t α oa hoa,
    {
      refl,
    },
    {
      simp only [bind', eq_self_iff_true, if_true, dite_eq_ite, heq_iff_eq, and_self],
    }
  end,
  bind_assoc := begin
    intros α β γ oa ob oc,
    simp only [bind_eq_bind'],
    induction oa with α a i t α oa hoa,
    {
      simp [bind'],
    },
    {
      by_cases hab : α = β,
      {
        induction hab,
        by_cases hb : ob = pure' α,
        {
          simp [hb],
        },
        {
          simp [bind'_of_ne_pure' _ _ _ _ hb],
          by_cases hac : α = γ,
          {
            induction hac,
            by_cases hc : oc = pure' α,
            {
              simp [hc, bind'_of_ne_pure' _ _ _ _ hb],
            },
            {
              simp [bind'_of_ne_pure' _ _ _ _ hc,
                hoa],
              by_cases h' : (λ (x : α), bind' α α (ob x) oc) = pure' α,
              {
                simp [h'],
              },
              {
                simp [bind'_of_ne_pure' _ _ _ _ h'],
              }
            }
          },
          {
            simp [bind'_of_ne _ _ _ _ hac, hoa],

          }
        }
      },
      {
        simp [bind'_of_ne _ _ _ _ hab],
        by_cases hbc : β = γ,
        {
          induction hbc,
          by_cases hc : oc = pure' β,
          {
            simp [hc, bind'_of_ne _ _ _ _ hab],
          },
          {
            simp [bind'_of_ne_pure' _ _ _ _ hc,
              bind'_of_ne _ _ _ _ hab, hoa],
          }
        },
        {
          by_cases hac : α = γ,
          {
            induction hac,
            simp [bind'_of_ne _ _ _ _ hab, bind'_of_ne _ _ _ _ hbc,
              hoa],
            by_cases h' : (λ (x : α), bind' β α (ob x) oc) = pure' α,
            {
              simp [h'],
            },
            {
              simp [bind'_of_ne_pure' _ _ _ _ h'],
            }
          },
          {
          simp [bind'_of_ne _ _ _ _ hab, bind'_of_ne _ _ _ _ hbc,
            bind'_of_ne _ _ _ _ hac, hoa],

          }
        }
      }
    },
  end }

end double