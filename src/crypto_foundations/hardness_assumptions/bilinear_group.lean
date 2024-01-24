/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import crypto_foundations.hardness_assumptions.hard_homogeneous_space

/-!
# Bilinear Homogenous Space

-/

open oracle_comp oracle_spec

class has_pairing (X₁ X₂ Xₜ : Type) :=
(pair' : X₁ → X₂ → Xₜ)

def pair {X₁ X₂ : Type} (Xₜ : Type) [has_pairing X₁ X₂ Xₜ]
  (x₁ : X₁) (x₂ : X₂) : Xₜ := has_pairing.pair' x₁ x₂

class bilinear_torsor (G X₁ X₂ Xₜ : Type) [add_comm_group G]
  extends has_pairing X₁ X₂ Xₜ :=
(add_torsor₁' : add_torsor G X₁)
(add_torsor₂' : add_torsor G X₂)
(add_torsorₜ' : add_torsor G Xₜ)
(pair_vadd_vadd (g g' : G) (x₁ : X₁) (x₂ : X₂) :
  pair Xₜ (g +ᵥ x₁) (g' +ᵥ x₂) = (g + g') +ᵥ (pair Xₜ x₁ x₂))

namespace bilinear_torsor

instance add_torsor₁ (G X₁ X₂ Xₜ : Type) [add_comm_group G] [bilinear_torsor G X₁ X₂ Xₜ] :
  add_torsor G X₁ := bilinear_torsor.add_torsor₁' X₂ Xₜ
instance add_torsor₂ (G X₁ X₂ Xₜ : Type) [add_comm_group G] [bilinear_torsor G X₁ X₂ Xₜ] :
  add_torsor G X₂ := bilinear_torsor.add_torsor₂' X₁ Xₜ
instance add_torsorₜ (G X₁ X₂ Xₜ : Type) [add_comm_group G] [bilinear_torsor G X₁ X₂ Xₜ] :
  add_torsor G Xₜ := bilinear_torsor.add_torsorₜ' X₁ X₂

end bilinear_torsor

-- variables {G X₁ X₂ Xₜ : Type} [add_comm_group G]

class bilinear_homogenous_space (G X₁ X₂ Xₜ : Type) [add_comm_group G]
  [fintype G] extends bilinear_torsor G X₁ X₂ Xₜ :=
[inhabited_X₁' : inhabited X₁] [inhabited_X₂' : inhabited X₂] [inhabited_Xₜ' : inhabited Xₜ]
(poly_time_pair : poly_time (function.uncurry (pair' : X₁ → X₂ → Xₜ)))

namespace bilinear_homogenous_space

instance inhabited_X₁ (G X₁ X₂ Xₜ : Type) [add_comm_group G] [fintype G]
  [bilinear_homogenous_space G X₁ X₂ Xₜ] : inhabited X₁ := inhabited_X₁' G X₂ Xₜ

noncomputable instance fintype_X₁ (G X₁ X₂ Xₜ : Type) [add_comm_group G] [fintype G]
  [bilinear_homogenous_space G X₁ X₂ Xₜ] : fintype X₁ :=
begin
  refine set.fintype_of_finite_univ _,
  have : set.range (λ g, g +ᵥ default : G → X₁) = set.univ,
  from set.eq_univ_of_forall (λ x, ⟨x -ᵥ default, vsub_vadd _ _⟩),
  refine this ▸ (set.finite_range (λ g, g +ᵥ default))
end

/-- Decisional Bilinear Diffie Hellman adversary -/
def dbdh_adv (G X Xₜ : Type) :=
sec_adv unif_spec (X × X × X × Xₜ) bool

/-- Decisional Bilinear Diffie Hellman experiment -/
noncomputable def dbhdh_exp (G X Xₜ : Type) [add_comm_group G] [fintype G]
  [bilinear_homogenous_space G X X Xₜ] (adv : dbdh_adv G X Xₜ) :
  sec_exp unif_spec bool bool :=
{ inp_gen := coin,
  main := λ b, do
    { x ←$ᵗ X, g₁ ←$ᵗ G, g₂ ←$ᵗ G,
        g₃ ←$ᵗ G, u ←$ᵗ G,  
      adv.run (g₁ +ᵥ x, g₂ +ᵥ x, g₃ +ᵥ x,
        if b then (g₁ + g₂ + g₃) +ᵥ pair Xₜ x x
          else u +ᵥ pair Xₜ x x) },
  is_valid := λ b b', b = b',
  .. base_oracle_algorithm }

end bilinear_homogenous_space