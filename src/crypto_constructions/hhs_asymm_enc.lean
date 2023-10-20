/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.primitives.asymm_encryption.asymm_enc_scheme
import crypto_foundations.hardness_assumptions.hard_homogeneous_space

/-!
# Symmetric-Key Encryption Schemes

This file defines symmetric key encryption schemes as well as their security properties.
-/

open oracle_comp oracle_spec algorithmic_homogenous_space asymm_enc_alg
open_locale ennreal

/-- Elgemal-style encryption on a hard homogenous space.
Messages are base points in `X` (in practice this is some encoding of messages),
The public key is a pair of base points in `X` chosen uniformly at random,
and the secret key is their vectorization in `G`. Signatures are also a pair of base points. -/
noncomputable def hhs_elgamal (G X : Type) [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X] :
  asymm_enc_alg X (X × X) G (X × X) :=
{ keygen := λ u, do
    { x₀ ←$ᵗ X, sk ←$ᵗ G,
      pk ← return (sk +ᵥ x₀),
      return ((x₀, pk), sk) },
  encrypt := λ ⟨m, x₀, pk⟩, do
    { g ←$ᵗ G, return (g +ᵥ x₀, m * (g +ᵥ pk)) },
  decrypt := λ ⟨⟨c₁, c₂⟩, sk⟩, do
    { return (c₂ / (sk +ᵥ c₁)) } }

namespace hhs_elgamal

section apply

variables (G X : Type) [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X]

@[simp] lemma keygen_apply (u : unit) : (hhs_elgamal G X).keygen u =
  do {x₀ ←$ᵗ X, sk ←$ᵗ G, pk ← return (sk +ᵥ x₀), return ((x₀, pk), sk)} := rfl

lemma fst_map_keygen_apply_dist_equiv (u : unit) :
  prod.fst <$> (hhs_elgamal G X).keygen () ≃ₚ
    do {x₀ ←$ᵗ X, sk ←$ᵗ G, return (x₀, sk +ᵥ x₀)} := sorry

@[simp] lemma encrypt_apply (z : X × (X × X)) : (hhs_elgamal G X).encrypt z =
  do {g ←$ᵗ G, return (g +ᵥ z.2.1, z.1 * (g +ᵥ z.2.2))} :=
by rcases z with ⟨m, x₀, pk⟩; refl

@[simp] lemma decrypt_apply (z : (X × X) × G) : (hhs_elgamal G X).decrypt z =
  return (z.1.2 / (z.2 +ᵥ z.1.1)) :=
by rcases z with ⟨⟨c₁, c₂⟩, sk⟩; refl

end apply

/-- Elgamal encryption always returns the correct decryption of arbitrary messages. -/
theorem is_sound (G X : Type) [add_comm_group G] [algorithmic_homogenous_space G X] [group X] :
  (hhs_elgamal G X).sound :=
begin
  rw [asymm_enc_alg.sound_iff_support_decrypt_eq],
  rintros m ⟨x₀, pk⟩ sk ⟨c₁, c₂⟩ hks hσ,
  have hpk : sk +ᵥ x₀ = pk,
  by simpa using hks,
  have hc : ∃ g : G, g +ᵥ x₀ = c₁ ∧ m * (g +ᵥ (sk +ᵥ x₀)) = c₂,
  by simpa [← hpk] using hσ,
  obtain ⟨g, hc₁, hc₂⟩ := hc,
  simp [← hc₁, ← hc₂, vadd_comm sk g x₀],
end

section ind_cpa

variables {G X : Type} [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X]

noncomputable def reduction (adv : (hhs_elgamal G X).ind_cpa_adversary) :
  decisional_parallelization_adversary G X :=
{ -- Try to check if `x₃` is the correct parallelization
  run := λ ⟨x₀, x₁, x₂, x₃⟩, do
    { ms ← adv.run (x₀, x₁),
      b ←$ᵗ bool,
      c ← return (x₂, (if b then ms.1 else ms.2) * x₃),
      b' ← adv.distinguish ((x₀, x₁), ms, c),
      return (b = b') } }

lemma prob_output_fair_decision_challenge_reduction (adv : (hhs_elgamal G X).ind_cpa_adversary) :
  ⁅= tt | fair_decision_challenge (reduction adv)⁆ = adv.advantage :=
begin
  refine dist_equiv.prob_output_eq _ _,
  rw [fair_decision_challenge],
  rw [ind_cpa_experiment],
  rw_dist_equiv [fst_map_keygen_apply_dist_equiv G X ()],
  refine trans _ ((bind_bind_dist_equiv_assoc _ _ _)),
  pairwise_dist_equiv 1,
  refine trans _ ((bind_bind_dist_equiv_assoc _ _ _)),
  pairwise_dist_equiv 1,
  rw_dist_equiv [return_bind_dist_equiv, return_bind_dist_equiv],
  refine trans (bind_bind_dist_equiv_comm _ _ _) _,
  pairwise_dist_equiv 1,
  refine trans (bind_bind_dist_equiv_comm _ _ _) _,
  pairwise_dist_equiv 1,
  rw [encrypt_apply],
  refine trans _ ((bind_bind_dist_equiv_assoc _ _ _)),
  pairwise_dist_equiv 1,
end

lemma prob_output_unfair_decision_challenge_reduction (adv : (hhs_elgamal G X).ind_cpa_adversary) :
  ⁅= tt | unfair_decision_challenge (reduction adv)⁆ = 1 / 2 :=
begin
  rw [unfair_decision_challenge],
  refine prob_output_uniform_bind_of_const (λ x₀, _),
  refine prob_output_uniform_bind_of_const (λ g₁, _),
  refine prob_output_uniform_bind_of_const (λ g₂, _),
  refine prob_output_uniform_bind_of_const (λ g₃, _),
  rw [reduction],
  simp only [reduction],
  rw [prob_output_bnot_map],
  have : ⁅= ff | $ᵗ bool⁆ = 1 / 2 := sorry,
  refine trans _ this,
  by_dist_equiv,
  rw_dist_equiv [return_bind_dist_equiv],
  refine trans (bind_bind_dist_equiv_comm _ _ _) _,
  refine trans (bind_dist_equiv_bind_of_dist_equiv_right _ _ _
    (λ _ _, (bind_bind_dist_equiv_assoc _ _ _))) _,
  sorry -- Need to show that the uniformity "cancels out".
end

theorem reduction_advantage (adv : (hhs_elgamal G X).ind_cpa_adversary) :
  (adv.advantage + 1 / 2) / 2 = (reduction adv).advantage :=
by rw [advantage_eq_prob_output_fair_add_prob_output_unfair,
  prob_output_unfair_decision_challenge_reduction,
  prob_output_fair_decision_challenge_reduction]

end ind_cpa

end hhs_elgamal