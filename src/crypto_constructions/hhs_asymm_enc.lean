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

open oracle_comp oracle_spec algorithmic_homogenous_space asymm_enc_alg
open_locale ennreal

/-- Elgemal-style encryption on a hard homogenous space.
Messages are base points in `X` (in practice this is some encoding of messages),
The public key is a pair of base points in `X` chosen uniformly at random,
and the secret key is their vectorization in `G`. Signatures are also a pair of base points. -/
noncomputable def hhs_elgamal (G X : Type) [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X] :
  asymm_enc_alg unif_spec X (X × X) G (X × X) :=
{ keygen := λ u, do
    { x₀ ←$ᵗ X, sk ←$ᵗ G,
      pk ← return (sk +ᵥ x₀),
      return ((x₀, pk), sk) },
  encrypt := λ ⟨m, x₀, pk⟩, do
    { g ←$ᵗ G, return (g +ᵥ x₀, m * (g +ᵥ pk)) },
  decrypt := λ ⟨⟨c₁, c₂⟩, sk⟩, do
    { return (c₂ / (sk +ᵥ c₁)) },
  .. base_oracle_algorithm }

namespace hhs_elgamal

section apply

variables (G X : Type) [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X]

@[simp] lemma keygen_apply (u : unit) : (hhs_elgamal G X).keygen u =
  do {x₀ ←$ᵗ X, sk ←$ᵗ G, pk ← return (sk +ᵥ x₀), return ((x₀, pk), sk)} := rfl

@[simp] lemma encrypt_apply (z : X × (X × X)) : (hhs_elgamal G X).encrypt z =
  do {g ←$ᵗ G, return (g +ᵥ z.2.1, z.1 * (g +ᵥ z.2.2))} :=
match z with | ⟨m, x₀, pk⟩ := rfl end

@[simp] lemma decrypt_apply (z : (X × X) × G) : (hhs_elgamal G X).decrypt z =
  return (z.1.2 / (z.2 +ᵥ z.1.1)) :=
match z with | ⟨⟨c₁, c₂⟩, sk⟩ := rfl end

@[simp] lemma to_oracle_algorithm_eq : (hhs_elgamal G X).to_oracle_algorithm =
  base_oracle_algorithm := rfl

@[simp] lemma base_S_eq : (hhs_elgamal G X).base_S = unit := rfl

@[simp] lemma init_state_eq : (hhs_elgamal G X).init_state = () := rfl

@[simp] lemma base_oracle_eq : (hhs_elgamal G X).base_oracle = idₛₒ := rfl

end apply

/-- Elgamal encryption always returns the correct decryption of arbitrary messages. -/
theorem is_sound (G X : Type) [add_comm_group G] [algorithmic_homogenous_space G X] [group X] :
  (hhs_elgamal G X).is_sound :=
begin
  simp [is_sound_iff, prod.eq_iff_fst_eq_snd_eq],
  -- Pattern matching with `rfl` puts things in a very nice form
  rintros m m' ⟨x₀, pk⟩ sk u (rfl : sk +ᵥ x₀ = pk) x1 x2 u' g rfl rfl rfl,
  show m * (g +ᵥ (sk +ᵥ x₀)) / (sk +ᵥ (g +ᵥ x₀)) = m,
  by rw [vadd_vadd g sk, vadd_vadd sk g, add_comm g sk, mul_div_cancel''],
end

section ind_cpa

variables {G X : Type} [add_comm_group G]
  [algorithmic_homogenous_space G X] [group X]

noncomputable def ind_cpa_reduction (adv : (hhs_elgamal G X).ind_cpa_adv) :
  dec_parallelization_adv G X :=
{ run := λ ⟨x₀, x₁, x₂, x₃⟩, do
    { ms ← adv.run (x₀, x₁),
      b ←$ᵗ bool,
      c ← return (x₂, (if b then ms.1 else ms.2) * x₃),
      b' ← adv.distinguish ((x₀, x₁), ms, c),
      return (b = b') },
  run_qb := (query_count.of_nat (1 : ℕ) 1) + adv.run_qb + adv.distinguish_qb }

theorem reduction_advantage (adv : (hhs_elgamal G X).ind_cpa_adv) :
  (dec_parallelization_exp $ ind_cpa_reduction adv).advantage =
    ((ind_cpa_exp adv).advantage + 1 / 2) / 2 :=
begin
  simp only [decisional_parallelization_exp.advantage_eq_add, ind_cpa_exp.advantage_eq, map_bind,
    bind_assoc, ind_cpa_reduction, ite_mul, pure_bind, to_oracle_algorithm_eq, keygen_apply,
    map_pure, coe_coin_unif_spec, encrypt_apply, base_oracle_algorithm.exec_eq],
  congr' 2,
  { by_dist_equiv,
    rw_dist_equiv [bind_bind_dist_equiv_comm ($ᵗ bool), bind_bind_dist_equiv_comm ($ᵗ bool)],
    pairwise_dist_equiv 2 with x hx g₁ hg₁,
    rw_dist_equiv [bind_bind_dist_equiv_comm ($ᵗ bool), bind_bind_dist_equiv_comm ($ᵗ bool)],
    rw_dist_equiv [bind_bind_dist_equiv_comm ($ᵗ G)] },
  { refine prob_output_bind_of_const _ _ (λ x hx, _),
    refine prob_output_bind_of_const _ _ (λ g₁ hg₁, _),
    refine prob_output_bind_of_const _ _ (λ g₂ hg₂, _),
    rw [prob_output_bind_bind_comm ($ᵗ G)],
    refine prob_output_bind_of_const _ _ (λ ms hms, _),
    rw [prob_output_bind_bind_comm ($ᵗ G), prob_output_eq_one_div_two_iff, bool.bnot_ff],
    simp_rw [← bind_assoc ($ᵗ G)],
    let adv₀ := ($ᵗ G >>= λ g, adv.distinguish ((x, g₁ +ᵥ x), ms, g₂ +ᵥ x, (g +ᵥ x))),
    have : (fintype.card bool : ℝ≥0∞)⁻¹ = 1 / 2 := by simp,
    refine trans (prob_output_uniform_select_fintype_bind_bind_eq_of_const _ ⟨adv₀, λ b, _⟩) this,
    let f : G → G := λ g, ((ite b ms.1 ms.2)⁻¹ * (g +ᵥ x)) -ᵥ x,
    have hf : f.bijective := function.bijective.comp (vsub_bijective _)
      (function.bijective.comp (group.mul_left_bijective _) (vadd_bijective _)),
    rw_dist_equiv [uniform_select_fintype_bind_bij_dist_equiv G f hf],
    refine bind_dist_equiv_bind_of_dist_equiv_right' _ (λ g, _),
    cases b; simp }
end

end ind_cpa

end hhs_elgamal