/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.superpolynomial_decay

/-!
# Negligable Functions

This file defines the standard cryptographic notion of a negligable function.
The definition specializes mathlib's `superpolynomial_decay` definition.
-/

/-- `superpolynomial_decay` is a more general definition for more general spaces.
  This definition is meant to provide a cleaner API for cryptography proofs -/
def negligable {α : Type*} [topological_space α] [comm_semiring α]
  (f : ℕ → α) : Prop := 
asymptotics.superpolynomial_decay filter.at_top coe f
