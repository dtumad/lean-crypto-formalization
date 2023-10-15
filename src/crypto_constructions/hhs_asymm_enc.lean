/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.primitives.asymm_enc
import crypto_foundations.hardness_assumptions.hard_homogeneous_space

/-!
# Symmetric-Key Encryption Schemes

This file defines symmetric key encryption schemes as well as their security properties.
-/

open oracle_comp oracle_spec

/-- Elgemal-style encryption on a hard homogenous space. -/
noncomputable def hhs_elgamal (G X : Type) [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X] :
  asymm_enc_alg X (X × X) G (X × X) :=
{ keygen := λ u, do
    { x₀ ←$ᵗ X, sk ←$ᵗ G,
      return ((x₀, sk +ᵥ x₀), sk) },
  encrypt := λ ⟨m, x₀, pk⟩, do
    { g ←$ᵗ G, return (g +ᵥ x₀, m * (g +ᵥ pk)) },
  decrypt := λ ⟨⟨c₁, c₂⟩, sk⟩, do
    { return (c₂ / (sk +ᵥ c₁)) } }

namespace hhs_elgamal

section apply

variables (G X : Type) [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X]

@[simp] lemma keygen_apply (u : unit) : (hhs_elgamal G X).keygen u =
  do { x₀ ←$ᵗ X, sk ←$ᵗ G, return ((x₀, sk +ᵥ x₀), sk) } := rfl

@[simp] lemma encrypt_apply (z : X × (X × X)) : (hhs_elgamal G X).encrypt z =
  do { g ←$ᵗ G, return (g +ᵥ z.2.1, z.1 * (g +ᵥ z.2.2)) } :=
by rcases z with ⟨m, x₀, pk⟩; refl

@[simp] lemma decrypt_apply (z : (X × X) × G) : (hhs_elgamal G X).decrypt z =
  return (z.1.2 / (z.2 +ᵥ z.1.1)) :=
by rcases z with ⟨⟨c₁, c₂⟩, sk⟩; refl

end apply

section sound

variables (G X : Type) [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X]

/-- Elgamal encryption always returns the correct decryption of arbitrary messages. -/
lemma is_sound : (hhs_elgamal G X).sound :=
begin
  rw [asymm_enc_alg.sound_iff_support_decrypt_eq],
  rintros m ⟨x₀, pk⟩ sk ⟨c₁, c₂⟩ hks hσ,
  have hpk : sk +ᵥ x₀ = pk,
  by simpa only [keygen_apply, support_bind, support_uniform_select_fintype, set.top_eq_univ,
    set.mem_univ, support_bind_return, set.image_univ, set.Union_true, set.mem_Union,
    set.mem_range, prod.mk.inj_iff, exists_eq_right, exists_eq_left] using hks,
  have hc : ∃ g : G, g +ᵥ x₀ = c₁ ∧ m * (g +ᵥ (sk +ᵥ x₀)) = c₂,
  by simpa only [← hpk, encrypt_apply, support_bind_return, support_uniform_select_fintype,
    set.top_eq_univ, set.image_univ, set.mem_range, prod.mk.inj_iff] using hσ,
  obtain ⟨g, hc₁, hc₂⟩ := hc,
  simp only [← hc₁, ← hc₂, decrypt_apply, support_return, set.singleton_eq_singleton_iff,
    vadd_comm sk g x₀, mul_div_cancel''],
end

end sound

section ind_cpa

variables {G X : Type} [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X]

noncomputable def reduction (adv : (hhs_elgamal G X).ind_cpa_adversary) :
  algorithmic_homogenous_space.decisional_parallelization_adversary G X :=
{ -- Try to check if `x₃` is the correct parallelization
  run := λ ⟨x₀, x₁, x₂, x₃⟩, do
    { ⟨m₁, m₂⟩ ← adv.run (x₀, x₁), b ← coin,
      b' ← adv.distinguish ((x₀, x₁), m₁, m₂,
        (x₂, (if b then m₁ else m₂) * x₃)),
      return (b = b') },
  qb := adv.qb + (query_count.of_nat (1 : ℕ) 1)}

theorem reduction_advantage (adv : (hhs_elgamal G X).ind_cpa_adversary) :
  adv.advantage / 2 ≤ (reduction adv).advantage :=
begin
  sorry
end

end ind_cpa

end hhs_elgamal