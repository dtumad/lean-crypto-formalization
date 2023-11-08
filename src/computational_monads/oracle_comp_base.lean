/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import computational_monads.oracle_spec
import probability.probability_mass_function.basic

universes u v

-- namespace test

-- /-- Type to represent computations with access so oracles specified by and `oracle_spec`. -/
-- inductive oracle_comp (spec : oracle_spec) : Type → Type 1
-- | pure' (α : Type) (a : α) : oracle_comp α
-- | bind' (α β : Type) (oa : oracle_comp α) (ob : α → oracle_comp β) : oracle_comp β
-- | query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

-- open oracle_comp

-- open_locale classical

-- noncomputable def merge {spec : oracle_spec} {α β : Type}
--   (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
--   oracle_comp spec β :=
-- if h : α = β then (if h.rec_on ob = pure' β then h.rec_on oa
--   else bind' α β oa ob) else bind' α β oa ob

-- noncomputable def lawful_bind {spec : oracle_spec} : Π (α β : Type),
--   oracle_comp spec α → (α → oracle_comp spec β)
--     → oracle_comp spec β
-- | _ γ (pure' α a) oc := oc a
-- | _ γ (bind' α β oa ob) oc := merge oa (λ x, merge (ob x) oc)
-- | _ γ (query i t) oc := merge (query i t) oc

-- noncomputable instance (spec : oracle_spec) : monad (oracle_comp spec) :=
-- { pure := pure',
--   bind := lawful_bind }

-- instance (spec : oracle_spec) : is_lawful_monad (oracle_comp spec) :=
-- {
--   pure_bind := begin
--     intros,
--     refl,
--   end,
--   bind_assoc := begin
--     intros,
--     sorry,
--   end,
--   id_map := begin
--     intros α oa,
--     show lawful_bind _ _ _ _ = _,
--     induction oa with α a α β oa ob hoa hob i t,
--     simp [lawful_bind, merge],
--     {

--       by_cases hab : α = β,
--       {
--         induction hab,
--         rw [lawful_bind],
--         simp only [merge, eq_self_iff_true],
--         simp only [eq_self_iff_true, function.comp.right_id, if_true, dite_eq_ite],
--         simp [lawful_bind, merge] at ⊢ hoa hob,
--         intro hoba,
--         refine hoa.symm.trans _,
--         rw [hoba],
--       }
--     },
--     simp [lawfull_bind, merge],
--   end,
--   map_pure := begin
--     sorry
--   end,
--   pure_seq_eq_map := begin
--     sorry,
--   end,
-- }

-- end test

open oracle_spec

inductive oracle_comp_base (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp_base α
| query' (i : spec.ι) (t : spec.domain i) : oracle_comp_base (spec.range i)
| query_bind' (i : spec.ι) (t : spec.domain i) (α : Type)
    (ou : spec.range i → oracle_comp_base α) : oracle_comp_base α

namespace oracle_comp_base

open oracle_comp_base

section is_reduced

open_locale classical

def is_reduced (spec : oracle_spec) : Π (α : Type),
  oracle_comp_base spec α → Prop
| _ (pure' α a) := true
| _ (query' i t) := true
| _ (query_bind' i t α ou) := begin
  refine (∀ u, is_reduced α (ou u)) ∧ _,
  refine (if h : α = spec.range i then _ else true),
  refine h.rec_on ou ≠ pure' (spec.range i),
end

end is_reduced

def bind' {spec : oracle_spec} : Π (α β : Type),
  oracle_comp_base spec α → (α → oracle_comp_base spec β) →
    oracle_comp_base spec β
| _ β (pure' α a) ob := ob a
| _ β (query' i t) ob := query_bind' i t β ob
| _ β (query_bind' i t α ou) ob :=
        query_bind' i t β (λ u, bind' α β (ou u) ob)

lemma pure'_bind' {spec : oracle_spec} {α β : Type}
  (a : α) (ob : α → oracle_comp_base spec β) :
  bind' α β (pure' α a) ob = ob a := rfl

lemma bind'_assoc {spec : oracle_spec} {α β γ : Type}
  (oa : oracle_comp_base spec α) (ob : α → oracle_comp_base spec β)
  (oc : β → oracle_comp_base spec γ) :
  bind' β γ (bind' α β oa ob) oc =
    bind' α γ oa (λ x, bind' β γ (ob x) oc) :=
begin
  induction oa with α a i t i t α ou h,
  { simp [bind'] },
  { simp [bind'] },
  { simp [bind'],
    refine funext (λ u, h u ob) }
end

section reduce

open_locale classical

noncomputable def reduce {spec : oracle_spec} : Π {α : Type},
  oracle_comp_base spec α → oracle_comp_base spec α
| _ (pure' α a) := pure' α a
| _ (query' i t) := query' i t
| _ (query_bind' i t α ou) := begin
  refine (if h : α = spec.range i then _ else _),
  {
    -- induction h,
    refine if h.rec_on (λ u, reduce (ou u)) = pure' (spec.range i) then
      h.symm.rec_on (query' i t) else _,
    refine query_bind' i t α (λ u, reduce (ou u)),
  },
  refine query_bind' i t α (λ u, reduce (ou u))
end

-- lemma reduce_bind' {spec : oracle_spec} {α : Type}
--   (oa : oracle_comp_base spec α) :

@[simp] lemma reduce_idem {spec : oracle_spec} {α : Type}
  (oa : oracle_comp_base spec α) : oa.reduce.reduce = oa.reduce :=
begin
  induction oa with α a i t i t α ou h,
  { refl },
  { refl },
  {
    by_cases hα : spec.range i = α,
    { induction hα,
      simp [reduce],
      split_ifs with h',
      {
        simp [reduce],
      },
      {
        simp [reduce, h, h'],
      }
    },
    { simp [reduce, bind', ne.symm hα, h],

     }
  }
end

@[simp] lemma reduce_bind_pure {spec : oracle_spec} {α : Type}
  (oa : oracle_comp_base spec α) :
  reduce (bind' α α oa (pure' α)) = reduce oa :=
begin
  induction oa with α a i t i t α ou h,
  { simp [reduce, bind'] },
  { simp [reduce, bind'] },
  { by_cases hα : α = spec.range i,
    { simp [reduce, bind', hα, h] },
    { simp [reduce, bind', hα, h] } },
end

end reduce

instance setoid (spec : oracle_spec) (α : Type) :
  setoid (oracle_comp_base spec α) :=
{ r := λ oa oa', reduce oa = reduce oa',
  iseqv := ⟨λ _, rfl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩ }

end oracle_comp_base

-- def oracle_comp (spec : oracle_spec) (α : Type) : Type 1 :=
-- quotient (oracle_comp_base.setoid spec α)

def oracle_comp (spec : oracle_spec) (α : Type) : Type 1 :=
{oa // oracle_comp_base.is_reduced spec α oa}

namespace oracle_comp

open oracle_comp_base

section bind'

open_locale classical

noncomputable def bind' {spec : oracle_spec} : Π (α β : Type),
  oracle_comp spec α → (α → oracle_comp spec β) →
    oracle_comp spec β
| _ β ⟨pure' α a, h⟩ ob := ob a
| _ β ⟨query' i t, h⟩ ob :=
    begin
      refine if h : β = spec.range i then _ else
        ⟨query_bind' i t _ (λ u, (ob u).1), _⟩,
      {
        sorry,
      },
      {
        simp [is_reduced, h],
        refine λ u, (ob u).2,
      }
    end
| _ β ⟨query_bind' i t α ou, h⟩ ob :=
    begin
      let ov : spec.range i → oracle_comp spec β :=
        λ u, bind' α β ⟨ou u, h.1 u⟩ ob,
      refine ⟨query_bind' i t β (λ u, (ov u).1), λ u, _, _⟩,
      {
        -- simp [is_reduced] at ⊢ h,
        exact (ov u).2,
      },
      {
        rw [is_reduced] at h,
        by_cases hβ : spec.range i = β,
        {
          induction hβ,
          simp [ov] at ⊢ h,
          rw [function.funext_iff, not_forall],

        }
      }
    end

end bind'

-- open

-- noncomputable instance monad (spec : oracle_spec) :
--   monad (oracle_comp spec) :=
-- { pure := λ α a, ⟦oracle_comp_base.pure' α a⟧,
--   bind := λ α β oa ob, begin
--     refine quotient.lift_on oa (λ oa', ⟦_⟧) (λ oa₁ oa₂ h, _),
--     refine oracle_comp_base.bind' α β
--       (oracle_comp_base.reduce oa')
--       (λ x, quotient.lift_on (ob x) oracle_comp_base.reduce
--       (λ ob₁ ob₂ h, h)),
--     refine quotient.eq.2 (by congr; exact h),
--   end }

-- lemma pure_def {spec : oracle_spec} {α : Type} (a : α) :
--   (pure a : oracle_comp spec α) = ⟦oracle_comp_base.pure' α a⟧ := rfl

-- lemma bind_def {spec : oracle_spec} {α β : Type}
--   (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
--   oa >>= ob = begin
-- refine quotient.lift_on oa (λ oa', ⟦_⟧) (λ oa₁ oa₂ h, _),
--     refine oracle_comp_base.bind' α β
--       (oracle_comp_base.reduce oa')
--       (λ x, quotient.lift_on (ob x) oracle_comp_base.reduce
--       (λ ob₁ ob₂ h, h)),
--     refine quotient.eq.2 (by congr; exact h),
--   end  := rfl


-- instance is_lawful_monad (spec : oracle_spec) :
--   is_lawful_monad (oracle_comp spec) :=
-- { pure_bind := λ α β a ob, begin

--     simp [bind_def, pure_def, oracle_comp_base.reduce],
--     obtain ⟨ob', h⟩ := quotient.exists_rep (ob a),
--     refine trans _ h,
--     refine quotient.sound _,
--     show oracle_comp_base.reduce _ = oracle_comp_base.reduce _,
--     simp [oracle_comp_base.bind', oracle_comp_base.reduce, ← h],
--     -- simp [oracle_comp_base.reduce, ← h],
--   end,
--   bind_assoc := λ α β γ oa ob oc, begin
--     simp [bind_def, pure_def, oracle_comp_base.reduce],
--     obtain ⟨oa', h⟩ := quotient.exists_rep oa,
--     simp [← h],
--     show oracle_comp_base.reduce _ = oracle_comp_base.reduce _,
--     sorry,
--   end,
--   id_map := λ α oa, begin

--     show oa >>= (λ x, pure x) = oa,
--     simp [bind_def, pure_def, oracle_comp_base.reduce],
--     obtain ⟨oa', h⟩ := quotient.exists_rep oa,
--     simp [← h],
--     -- refine quotient.sound _,
--     show oracle_comp_base.reduce _ = oracle_comp_base.reduce _,
--     simp,
--     -- simp [oracle_comp_base.reduce_pure,
--     --   oracle_comp_base.extract_pure, ← h],
--     -- by_cases ha : ∃ a, oa'.reduce_pure.extract_pure = some a,
--     -- {
--     --   obtain ⟨a, ha⟩ := ha,
--     --   simp [ha, oracle_comp_base.reduce_pure],
--     --   induction oa',
--     --   {
--     --     simp [oracle_comp_base.reduce_pure,
--     --       oracle_comp_base.extract_pure] at ha,
--     --     simp [ha, oracle_comp_base.reduce_pure]
--     --   },
--     --   {

--     --     simp [oracle_comp_base.extract_pure_eq_some_iff] at ha,
--     --     exact symm ha,
--     --   },
--     --   {
--     --     simp [oracle_comp_base.extract_pure_eq_some_iff,
--     --       oracle_comp_base.reduce_pure] at ha,
--     --     exact false.elim ha,
--     --   }
--     -- },
--     -- {
--     --   rw [← option.is_some_iff_exists] at ha,
--     --   simp [option.is_none_iff_eq_none] at ha,
--     --   simp [ha, oracle_comp_base.reduce_pure],
--     -- }
--   end }

end oracle_comp
