/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import computational_monads.oracle_spec

universes u v

inductive is_lawfully_equiv (m : Type u → Type v) [monad m] :
  Π {α : Type u}, m α → m α → Prop
| refl {α : Type u} (x : m α) : is_lawfully_equiv x x
| symm {α : Type u} (x y : m α) (h : is_lawfully_equiv x y) :
    is_lawfully_equiv y x
| trans {α : Type u} (x y z : m α) (h : is_lawfully_equiv x y) (h' : is_lawfully_equiv y z) :
    is_lawfully_equiv x z
| pure_bind {α β : Type u} (a : α) (y : α → m β) :
    is_lawfully_equiv (pure a >>= y) (y a)
| bind_assoc {α β γ : Type u} (x : m α) (y : α → m β) (z : β → m γ) :
    is_lawfully_equiv ((x >>= y) >>= z) (x >>= λ a, (y a >>= z))
| map_id {α : Type u} (x : m α) :
    is_lawfully_equiv (x >>= pure) x
| bind_congr {α β : Type u} (x x' : m α) (y y' : α → m β)
    (hx : is_lawfully_equiv x x') (hy : ∀ a, is_lawfully_equiv (y a) (y' a)) :
    is_lawfully_equiv (x >>= y) (x' >>= y')

-- #check is_lawfully_equiv.bind_assoc
-- -- def lawfully_reduce (m : Type u → Type v)

lemma is_lawfully_equiv.equivalence (m : Type u → Type v) [monad m] (α : Type u) :
  equivalence (@is_lawfully_equiv m _ α) :=
⟨is_lawfully_equiv.refl, is_lawfully_equiv.symm, is_lawfully_equiv.trans⟩

open oracle_spec

/-- Type to represent computations with access so oracles specified by and `oracle_spec`. -/
inductive oracle_comp_base (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp_base α
| bind' (α β : Type) (oa : oracle_comp_base α) (ob : α → oracle_comp_base β) : oracle_comp_base β
| query (i : spec.ι) (t : spec.domain i) : oracle_comp_base (spec.range i)

namespace oracle_comp_base

def extract_pure {spec : oracle_spec} :
  Π {α : Type}, oracle_comp_base spec α → option α
| _ (pure' α a) := some a
| _ (bind' α β oa ob) := none
| _ (query i t) := none

lemma extract_pure_eq_some_iff {spec : oracle_spec} {α : Type}
  (oa : oracle_comp_base spec α) (a : α) :
  oa.extract_pure = some a ↔ oa = pure' α a :=
sorry

section reduce_pure

open_locale classical

noncomputable def reduce_pure {spec : oracle_spec} :
  Π {α : Type}, oracle_comp_base spec α → oracle_comp_base spec α
| _ (pure' α a) := pure' α a
| _ (bind' α β oa ob) := let oa' := reduce_pure oa in
  match extract_pure oa' with
  | (some a) := reduce_pure (ob a)
  | none := if h : β = α then
    (if h.rec_on (λ x, reduce_pure (ob x)) = (pure' α) then
      h.symm.rec oa' else bind' α β oa' (λ x, reduce_pure (ob x)))
        else bind' α β oa' (λ x, reduce_pure (ob x))
  end
| _ (query i t) := query i t

end reduce_pure

@[simp] lemma reduce_pure_idem {spec : oracle_spec} {α : Type}
  (oa : oracle_comp_base spec α) : reduce_pure (reduce_pure oa) = reduce_pure oa :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  {
    simp [reduce_pure],
  },
  {
    simp [reduce_pure],
    by_cases ha : ∃ a, oa.reduce_pure.extract_pure = some a,
    {
      obtain ⟨a, ha⟩ := ha,
      simp [ha, reduce_pure, hob],
    },
    {
      rw [← option.is_some_iff_exists] at ha,
      simp [option.is_none_iff_eq_none] at ha,
      simp [ha, reduce_pure],
      by_cases h : β = α,
      {
        induction h,
        simp,
        split_ifs with hb,
        {
          exact hoa,
        },
        {
          simp [reduce_pure, ha, hoa, hob, hb],
        }
      },
      {

        simp [h, reduce_pure, hoa, ha, hob],
      }
    }
  },
  {
    simp [reduce_pure]
  }
end

inductive assoc_equiv (spec : oracle_spec) :
  Π {α : Type}, oracle_comp_base spec α →
    oracle_comp_base spec α → Prop

instance setoid (spec : oracle_spec) (α : Type) :
  setoid (oracle_comp_base spec α) :=
{ r := λ oa oa', reduce_pure oa = reduce_pure oa',
  iseqv := ⟨λ _, rfl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩ }

-- instance setoid (spec : oracle_spec) (α : Type) :
--   setoid (oracle_comp_base spec α) :=
-- { r := λ oa oa', reduce oa = reduce oa',
--   iseqv := begin
--     refine ⟨_, _, _⟩,
--     {
--       intros oa,
--       induction oa,
--       simp [reduce],
--       simp [reduce],
--       simp [reduce],
--     },
--     {
--       intros oa oa',
--       refine λ h, _,
--       -- simp at h,
--       refine symm h,
--     },
--     {
--       intros oa oa' oa'' h h',
--       refine trans h h',
--     }
--   end }

end oracle_comp_base

def oracle_comp (spec : oracle_spec) (α : Type) : Type 1 :=
quotient (oracle_comp_base.setoid spec α)

namespace oracle_comp

noncomputable instance monad (spec : oracle_spec) :
  monad (oracle_comp spec) :=
{ pure := λ α a, ⟦oracle_comp_base.pure' α a⟧,
  bind := λ α β oa ob, begin
    refine quotient.lift_on oa (λ oa', ⟦_⟧) (λ oa₁ oa₂ h, _),
    refine oracle_comp_base.bind' α β
      (oracle_comp_base.reduce_pure oa')
      (λ x, quotient.lift_on (ob x) oracle_comp_base.reduce_pure
      (λ ob₁ ob₂ h, h)),
    refine quotient.eq.2 (by congr; exact h),
  end }

lemma pure_def {spec : oracle_spec} {α : Type} (a : α) :
  (pure a : oracle_comp spec α) = ⟦oracle_comp_base.pure' α a⟧ := rfl

lemma bind_def {spec : oracle_spec} {α β : Type}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  oa >>= ob = begin
refine quotient.lift_on oa (λ oa', ⟦_⟧) (λ oa₁ oa₂ h, _),
    refine oracle_comp_base.bind' α β
      (oracle_comp_base.reduce_pure oa')
      (λ x, quotient.lift_on (ob x) oracle_comp_base.reduce_pure
      (λ ob₁ ob₂ h, h)),
    refine quotient.eq.2 (by congr; exact h),

  end  := rfl


instance is_lawful_monad (spec : oracle_spec) :
  is_lawful_monad (oracle_comp spec) :=
{ pure_bind := λ α β a ob, begin
    simp [bind_def, pure_def, oracle_comp_base.reduce_pure],
    obtain ⟨ob', h⟩ := quotient.exists_rep (ob a),
    refine trans _ h,
    refine quotient.sound _,
    show oracle_comp_base.reduce_pure _ = oracle_comp_base.reduce_pure _,
    simp [oracle_comp_base.reduce_pure,
      oracle_comp_base.extract_pure, ← h],
  end,
  bind_assoc := begin

  end,
  id_map := λ α oa, begin
    show oa >>= (λ x, pure x) = oa,
    simp [bind_def, pure_def, oracle_comp_base.reduce_pure],
    obtain ⟨oa', h⟩ := quotient.exists_rep oa,
    simp [← h],
    -- refine quotient.sound _,
    show oracle_comp_base.reduce_pure _ = oracle_comp_base.reduce_pure _,
    simp [oracle_comp_base.reduce_pure,
      oracle_comp_base.extract_pure, ← h],
    by_cases ha : ∃ a, oa'.reduce_pure.extract_pure = some a,
    {
      obtain ⟨a, ha⟩ := ha,
      simp [ha, oracle_comp_base.reduce_pure],
      induction oa',
      {
        simp [oracle_comp_base.reduce_pure,
          oracle_comp_base.extract_pure] at ha,
        simp [ha, oracle_comp_base.reduce_pure]
      },
      {

        simp [oracle_comp_base.extract_pure_eq_some_iff] at ha,
        exact symm ha,
      },
      {
        simp [oracle_comp_base.extract_pure_eq_some_iff,
          oracle_comp_base.reduce_pure] at ha,
        exact false.elim ha,
      }
    },
    {
      rw [← option.is_some_iff_exists] at ha,
      simp [option.is_none_iff_eq_none] at ha,
      simp [ha, oracle_comp_base.reduce_pure],
    }
  end }

-- instance is_lawful_monad (spec : oracle_spec) :
--   is_lawful_monad (oracle_comp spec) :=
-- { pure_bind := begin
--     intros α β a ob,
--     rw [bind_eq_thing],
--     rw [pure_eq_thing],
--     simp [quotient.lift_on_mk, oracle_comp_base.reduce],
--     obtain ⟨ob', h⟩ := quotient.exists_rep (ob a),
--     refine trans _ h,
--     refine quotient.sound _,
--     show oracle_comp_base.reduce _ = oracle_comp_base.reduce _,
--     refine trans (oracle_comp_base.reduce_pure_bind _ _) _,
--     rw [←h],
--     simp,

--   end,
--   bind_assoc := begin
--     intros α β γ oa ob oc,
--     -- by_cases h : β = γ,
--     simp only [bind_eq_thing],
--     obtain ⟨oa', h⟩ := quotient.exists_rep oa,
--     simp [← h],
--     -- refine quotient.sound _,
--     show oracle_comp_base.reduce _ = oracle_comp_base.reduce _,
--     simp [oracle_comp_base.reduce_bind_assoc],
--   -- simp [quotient.lift_on_mk, oracle_comp_base.reduce],

--   end,
--   id_map := begin
--     intros α oa,
--     show oa >>= (λ x, pure x) = oa,
--     rw [bind_eq_thing],
--     obtain ⟨oa', h⟩ := quotient.exists_rep oa,
--     simp [← h],
--     show oracle_comp_base.reduce _ = oracle_comp_base.reduce _,
--     induction oa' with α a α β oa ob hoa hob i t,
--     {
--       simp [oracle_comp_base.reduce, bind_eq_thing, pure_eq_thing],
--     },
--     {
--       simp [oracle_comp_base.reduce, bind_eq_thing, pure_eq_thing],
--       simp [oracle_comp_base.reduce_bind_pure],
--     },
--     {
--       rw [oracle_comp_base.reduce],
--       rw [oracle_comp_base.reduce],

--       simp [oracle_comp_base.reduce, bind_eq_thing, pure_eq_thing],

--     }
--     -- rw [pure_eq_thing],
--     -- simp [quotient.lift_on_mk, oracle_comp_base.reduce],
--   end
-- }

end oracle_comp
