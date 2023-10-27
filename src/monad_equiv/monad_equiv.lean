/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import probability.borel_cantelli

/-!
# Lawful Equivalences Between Monads.

This file defines a typeclass `has_monad_equiv m` for monads equipped with an equivalence relation,
in the sense of having an equivalence relation on `m α` for any type `α`.

`has_lawful_monad_equiv` extends this to include rules about the equivalence being "well-behaved",
in the sense of respecting both the bind operation and the monad laws.

For simplicity we avoid defining an `is_monad_equiv` typeclass for general relations,
opting to only deal with the case of being equipped with a single global equivalence.
-/

universes u v

/-- Type for monads that have an equivalence `≃ₘ` on `m α` for any type `α`.
Purely syntactic, see `has_lawful_monad_equiv` for more well-behaved operations. -/
class has_monad_equiv (m : Type u → Type v) :=
(equivₘ : Π (α : Type u), m α → m α → Prop)

infix ` ≃ₘ ` : 50 := has_monad_equiv.equivₘ _

/-- `has_lawful_monad_equiv m` extends `has_monad_equiv` to behave better with monad operations.
Specifically it requires that the equivalence relation respects the bind operation `>>=`
in the sense that binding equivalent computations results in equivalent computations.
Finally we require that the monad is lawful up to the equivalence relation,
in the sense that the lawful monad conditions hold for the relation. -/
class has_lawful_monad_equiv (m : Type u → Type v) [monad m]
  extends has_monad_equiv m :=
(is_equiv' (α : Type u) : is_equiv (m α) (≃ₘ))
(bind_equiv_bind_of_equiv {α β : Type u} {ma ma' : m α} {mb mb' : α → m β} :
  ma ≃ₘ ma' → (∀ x, mb x ≃ₘ mb' x) → (ma >>= mb) ≃ₘ (ma' >>= mb'))
(pure_bind_equiv {α β : Type u} (x : α) (mb : α → m β) :
  (pure x >>= mb) ≃ₘ mb x)
(bind_equiv_assoc {α β γ : Type u} (ma : m α) (mb : α → m β) (mc : β → m γ) :
  ((ma >>= mb) >>= mc) ≃ₘ (ma >>= (λ x, mb x >>= mc)))

/-- Explicit instance for the `is_equiv` instance given by `has_monad_equiv`.
Allows the general `bind`, `symm`, and `trans` to be used for `≃ₘ`. -/
instance is_lawful_monad_equiv.is_equiv (m : Type u → Type v) [monad m]
  [has_lawful_monad_equiv m] (α : Type u) : is_equiv (m α) (≃ₘ) :=
has_lawful_monad_equiv.is_equiv' α

namespace has_lawful_monad_equiv

variables {m : Type u → Type v} [monad m] [hm : has_lawful_monad_equiv m] {α β γ : Type u}
include hm

@[simp] lemma equiv_self_iff_true (ma : m α) : ma ≃ₘ ma ↔ true := (iff_true _).2 (refl ma)

/-- special case of `bind_equiv_bind_of_equiv` with a constant right hand of the bind. -/
lemma bind_equiv_bind_of_equiv_left {ma ma' : m α} (h : ma ≃ₘ ma') (mb : α → m β) :
  (ma >>= mb) ≃ₘ (ma' >>= mb) :=
hm.bind_equiv_bind_of_equiv h (λ x, refl (mb x))

/-- special case of `bind_equiv_bind_of_equiv` with a constant left hand of the bind. -/
lemma bind_equiv_bind_of_equiv_right (ma : m α) {mb mb' : α → m β} (h : ∀ x, mb x ≃ₘ mb' x) :
  (ma >>= mb) ≃ₘ (ma >>= mb') :=
hm.bind_equiv_bind_of_equiv (refl ma) h

lemma bind_equiv_iff_of_equiv_left {ma ma' : m α} (h : ma ≃ₘ ma') (mb : α → m β)
  (mz : m β) : (ma >>= mb ≃ₘ mz) ↔ (ma' >>= mb ≃ₘ mz) :=
⟨trans (bind_equiv_bind_of_equiv_left (symm h) mb),
  trans (bind_equiv_bind_of_equiv_left h mb)⟩

lemma bind_equiv_iff_of_equiv_right (ma : m α) {mb mb' : α → m β} (h : ∀ x, mb x ≃ₘ mb' x)
  (mz : m β) : (ma >>= mb ≃ₘ mz) ↔ (ma >>= mb' ≃ₘ mz) :=
⟨trans (bind_equiv_bind_of_equiv_right ma (λ x, symm (h x))),
  trans (bind_equiv_bind_of_equiv_right ma h)⟩

@[simp] lemma pure_bind_equiv_iff (x : α) (mb : α → m β) (mz : m β) :
  (pure x >>= mb ≃ₘ mz) ↔ (mb x ≃ₘ mz) :=
⟨trans (symm $ hm.pure_bind_equiv x mb), trans (hm.pure_bind_equiv x mb)⟩

@[simp] lemma equiv_pure_bind_iff (x : α) (mb : α → m β) (mz : m β) :
  (mz ≃ₘ pure x >>= mb) ↔ (mz ≃ₘ mb x) :=
⟨λ h', trans h' (hm.pure_bind_equiv x mb),
  λ h', trans h' (symm $ hm.pure_bind_equiv x mb)⟩

lemma bind_equiv_iff_assoc (ma : m α) (mb : α → m β) (mc : β → m γ) (mz : m γ) :
  (((ma >>= mb) >>= mc) ≃ₘ mz) ↔ ((ma >>= (λ x, mb x >>= mc)) ≃ₘ mz) :=
⟨trans (symm $ hm.bind_equiv_assoc ma mb mc),
  trans (hm.bind_equiv_assoc ma mb mc)⟩

lemma equiv_bind_iff_assoc (ma : m α) (mb : α → m β) (mc : β → m γ) (mz : m γ) :
  (mz ≃ₘ ((ma >>= mb) >>= mc)) ↔ (mz ≃ₘ (ma >>= (λ x, mb x >>= mc))) :=
⟨λ h', trans h' (hm.bind_equiv_assoc ma mb mc),
  λ h', trans h' (symm $ hm.bind_equiv_assoc ma mb mc)⟩

section examples

/-- When the simplification is at the "outer level" the `simp` tactic works well. -/
example (mn : α → m α) (x : α) :
  (do {y ← pure x, mn y}) ≃ₘ
    (do {y ← pure x, z ← pure y, w ← pure z, mn z}) :=
by simp -- only [equiv_pure_bind_iff, equiv_self_iff_true]

/-- When the simplicition is nested inside of bind the `simp` tactic is much less helpful,
forcing us to manually "step in" to the bind in order for it to work. -/
example (mz : m β) (mn : β → m α) (x : α) :
  (do {y ← mz, z ← pure y, mn z}) ≃ₘ
    (do {y ← mz, z ← pure y, w ← pure z, mn z}) :=
bind_equiv_bind_of_equiv_right mz (by simp)

end examples

end has_lawful_monad_equiv