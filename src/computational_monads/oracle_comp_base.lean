/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

import computational_monads.oracle_spec

universes u v

-- inductive is_lawfully_equiv (m : Type u → Type v) [monad m] :
--   Π {α : Type u}, m α → m α → Prop
-- | refl {α : Type u} (x : m α) : is_lawfully_equiv x x
-- | symm {α : Type u} (x y : m α) (h : is_lawfully_equiv x y) :
--     is_lawfully_equiv y x
-- | trans {α : Type u} (x y z : m α) (h : is_lawfully_equiv x y)
--     (h' : is_lawfully_equiv y z) : is_lawfully_equiv x z
-- | pure_bind {α β : Type u} (a : α) (y : α → m β) :
--     is_lawfully_equiv (pure a >>= y) (y a)
-- | bind_assoc {α β γ : Type u} (x : m α) (y : α → m β) (z : β → m γ) :
--     is_lawfully_equiv ((x >>= y) >>= z) (x >>= λ a, (y a >>= z))


-- #check is_lawfully_equiv.bind_assoc
-- -- def lawfully_reduce (m : Type u → Type v)

-- lemma is_lawfully_equiv.equivalence (m : Type u → Type v) [monad m] (α : Type u) :
--   equivalence (@is_lawfully_equiv m _ α) :=
-- ⟨is_lawfully_equiv.refl, is_lawfully_equiv.symm, is_lawfully_equiv.trans⟩

open oracle_spec

/-- Type to represent computations with access so oracles specified by and `oracle_spec`. -/
inductive oracle_comp_base (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp_base α
| bind' (α β : Type) (oa : oracle_comp_base α) (ob : α → oracle_comp_base β) : oracle_comp_base β
| query (i : spec.ι) (t : spec.domain i) : oracle_comp_base (spec.range i)

namespace oracle_comp_base

instance monad (spec : oracle_spec) : monad (oracle_comp_base spec) :=
{ pure := oracle_comp_base.pure',
  bind := oracle_comp_base.bind' }

-- instance setoid (spec : oracle_spec) (α : Type) :
--   setoid (oracle_comp_base spec α) :=
-- { r := is_lawfully_equiv (oracle_comp_base spec),
--   iseqv := is_lawfully_equiv.equivalence (oracle_comp_base spec) α }

open_locale classical

noncomputable def reduce {spec : oracle_spec} :
  Π {α : Type}, oracle_comp_base spec α → oracle_comp_base spec α
| _ (pure' α a) := pure' α a
-- | _ (bind' _ _ oa (pure' _)) := oa
| _ (bind' _ β (pure' α a) ob) := ob a
| _ (bind' _ γ (bind' α β oa ob) oc) := begin
    refine if h : γ = β then _ else _,
    {
      induction h,
      refine if oc = pure' _ then (bind' α γ oa ob) else
        bind' α γ oa (λ x, bind' γ γ (ob x) oc)
    },
    refine bind' α γ oa (λ x, bind' β γ (ob x) oc)

  end
| _ (bind' _ β (query i t) ob) := begin
    refine if h : spec.range i = β then _ else _,
    {
      induction h,
      refine if ob = pure' _ then (query i t) else
        bind' _ _ (query i t) (λ x, (ob x)),
    },
    -- refine if ob = pure' _ then _ else _,
    refine bind' _ _ (query i t) (λ x, (ob x))
  end
| _ (query i t) := query i t

lemma reduce_pure_bind {spec : oracle_spec} {α β : Type}
  (a : α) (ob : α → oracle_comp_base spec β) :
  reduce (bind' α β (pure' α a) ob) = ob a := rfl

lemma reduce_bind_pure {spec : oracle_spec} {α : Type}
  (oa : oracle_comp_base spec α) :
  reduce (bind' α α oa (pure' α)) = oa :=
begin
  induction oa with α a α β oa ob hoa hob i t,
  {
    simp [reduce],
  },
  {
    rw [reduce],
    simp [reduce, eq_self_iff_true, heq_iff_eq, true_and],
  },
  {
    simp [reduce],
  }
end

instance setoid (spec : oracle_spec) (α : Type) :
  setoid (oracle_comp_base spec α) :=
{ r := λ oa oa', reduce oa = reduce oa',
  iseqv := begin
    refine ⟨_, _, _⟩,
    {
      intros oa,
      induction oa,
      simp [reduce],
      simp [reduce],
      simp [reduce],
    },
    {
      intros oa oa',
      refine λ h, _,
      -- simp at h,
      refine symm h,
    },
    {
      intros oa oa' oa'' h h',
      refine trans h h',
    }
  end }

end oracle_comp_base

-- def oracle_comp (spec : oracle_spec) (α : Type) : Type 1 :=
-- quot (@is_lawfully_equiv (oracle_comp_base spec) _ α)

def oracle_comp (spec : oracle_spec) (α : Type) : Type 1 :=
quotient (oracle_comp_base.setoid spec α)

namespace oracle_comp

-- @[simp] lemma equiv_iff (spec : oracle_spec) (α : Type)
--   (oa oa' : oracle_comp spec α) : oa ≈ oa'

noncomputable instance monad (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := λ α a, ⟦oracle_comp_base.pure' α a⟧,
  bind := λ α β oa ob, begin
    refine quotient.lift_on oa (λ oa', ⟦_⟧) (λ oa₁ oa₂ h, _),
    refine oracle_comp_base.bind' α β
      (oracle_comp_base.reduce oa')
      (λ x, quotient.lift_on (ob x) oracle_comp_base.reduce
      (λ ob₁ ob₂ h, h)),
    refine quotient.eq.2 (by congr; exact h),
    -- simp only [quotient.eq],
    -- simp [h],
    -- congr,
    -- exact h,
  end }

lemma pure_eq_thing {spec : oracle_spec} {α : Type} (a : α) :
  (pure a : oracle_comp spec α) = ⟦oracle_comp_base.pure' α a⟧ := rfl

lemma bind_eq_thing {spec : oracle_spec} {α β : Type}
  (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  oa >>= ob = begin
refine quotient.lift_on oa (λ oa', ⟦_⟧) (λ oa₁ oa₂ h, _),
    refine oracle_comp_base.bind' α β
      (oracle_comp_base.reduce oa')
      (λ x, quotient.lift_on (ob x) oracle_comp_base.reduce
      (λ ob₁ ob₂ h, h)),
    refine quotient.eq.2 (by congr; exact h),

  end  := rfl


instance is_lawful_monad (spec : oracle_spec) :
  is_lawful_monad (oracle_comp spec) :=
{ pure_bind := begin
    intros α β a ob,
    rw [bind_eq_thing],
    rw [pure_eq_thing],
    simp [quotient.lift_on_mk, oracle_comp_base.reduce],
    obtain ⟨ob', h⟩ := quotient.exists_rep (ob a),
    refine trans _ h,
    refine quotient.sound _,
    show oracle_comp_base.reduce _ = oracle_comp_base.reduce _,
    refine trans (oracle_comp_base.reduce_pure_bind _ _) _,
    rw [←h],
    simp,

  end,
  bind_assoc := begin
    sorry
  end,
  id_map := begin
    intros α oa,
    show oa >>= (λ x, pure x) = oa,
    rw [bind_eq_thing],
    obtain ⟨oa', h⟩ := quotient.exists_rep oa,
    simp [← h],
    show oracle_comp_base.reduce _ = oracle_comp_base.reduce _,
    induction oa' with α a α β oa ob hoa hob i t,
    {
      simp [oracle_comp_base.reduce, bind_eq_thing, pure_eq_thing],
    },
    {
      simp [oracle_comp_base.reduce, bind_eq_thing, pure_eq_thing],
      simp [oracle_comp_base.reduce_bind_pure],
    },
    {
      rw [oracle_comp_base.reduce],
      rw [oracle_comp_base.reduce],

      simp [oracle_comp_base.reduce, bind_eq_thing, pure_eq_thing],

    }
    -- rw [pure_eq_thing],
    -- simp [quotient.lift_on_mk, oracle_comp_base.reduce],
  end
}

end oracle_comp
