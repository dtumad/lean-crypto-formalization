/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import control.applicative

/-!
# Monadic Product

This file defines a `mprod` function for running two monads independently,
collection their results in a product type
-/

def mprod {m : Type → Type 1} [monad m] {α β : Type} (x : m α) (y : m β) : m (α × β) :=
-- (×) <$> x <*> y
do {a ← x, b ← y, return (a, b)}

lemma mprod.def {m : Type* → Type*} [monad m] {α β : Type*} (x : m α) (y : m β) :
mprod x y = do {a ← x, b ← y, return (a, b)} := rfl

infixr `×ₘ` : 40 := mprod