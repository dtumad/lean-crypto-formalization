import group_theory.group_action

/-!
# Free, Transative, and Principal group actions.

Defines type classes for group actions that are (in/sur/bi)jective maps on the base type
-/

section action_classes

/-- Mixin typeclass for free actions, where the action of group elements is injective -/
class free_action_class (G X : Type*) [add_monoid G] [add_action G X] : Prop :=
(free (x : X) : function.injective (λ g, g +ᵥ x : G → X))

/-- Mixin typeclass for transitive actions, where the action of group elements is surjective -/
class transitive_action_class (G X : Type*) [add_monoid G] [add_action G X] : Prop :=
(trans (x : X) : function.surjective (λ g, g +ᵥ x : G → X))

/-- Mixin typeclass for actions that are both free and transitive -/
class principal_action_class (G X : Type*) [add_monoid G] [add_action G X]
  extends free_action_class G X, transitive_action_class G X : Prop

variables {G X : Type*} [add_monoid G] [add_action G X]

@[simp]
lemma free_action_class.vadd_eq_iff [free_action_class G X] 
  (x : X) (g g' : G) : g +ᵥ x = g' +ᵥ x ↔ g = g' :=
⟨λ hx, free_action_class.free x hx, λ h, congr_arg _ h⟩

lemma free_action_class.eq_of_vadd_eq [free_action_class G X] 
  (x : X) {g g' : G} (h : g +ᵥ x = g' +ᵥ x) : g = g' :=
(free_action_class.vadd_eq_iff x g g').mp h

lemma transitive_action_class.exists_vadd_eq [transitive_action_class G X]
  (x y : X) : ∃ (g : G), g +ᵥ x = y :=
transitive_action_class.trans x y

lemma principal_action_class_iff_bijective :
  principal_action_class G X ↔ ∀ x, function.bijective (λ g, g +ᵥ x : G → X) :=
begin
  split,
  { introsI h x,
    refine ⟨free_action_class.free x, transitive_action_class.trans x⟩ },
  { intro h,
    haveI : free_action_class G X := { free := λ x, (h x).1 },
    haveI : transitive_action_class G X := { trans := λ x, (h x).2 },
    exact {} }
end

theorem principal_action_class.vectorization_unique [principal_action_class G X] 
  (x y : X) : ∃! (g : G), g +ᵥ x = y :=
exists_unique_of_exists_of_unique (transitive_action_class.exists_vadd_eq x y)
  (λ g g' hg hg', free_action_class.eq_of_vadd_eq x (hg.trans hg'.symm))

variables (G X)

lemma free_action_class.card_le_card [free_action_class G X]
  [fintype G] [fintype X] [inhabited X] :
  fintype.card G ≤ fintype.card X :=
fintype.card_le_of_injective (λ g, g +ᵥ (arbitrary X)) (free_action_class.free $ arbitrary X)

lemma transitive_action_class.card_le_card [transitive_action_class G X]
  [fintype G] [fintype X] [inhabited X] :
  fintype.card X ≤ fintype.card G :=
fintype.card_le_of_surjective (λ g, g +ᵥ (arbitrary X)) (transitive_action_class.trans $ arbitrary X)

theorem principal_action_class.fintype_card_eq [principal_action_class G X]
  [fintype G] [fintype X] [inhabited X] :
  fintype.card G = fintype.card X :=
le_antisymm (free_action_class.card_le_card G X) (transitive_action_class.card_le_card G X)

noncomputable def principal_action_class.equiv [principal_action_class G X]
  [fintype G] [fintype X] [inhabited X] : G ≃ X :=
fintype.equiv_of_card_eq (principal_action_class.fintype_card_eq G X)

variables {G X}

section vectorization

variable (G)

/-- The vectorization of `x` and `y` is the unique element of `g` sending `x` to `y` under the action.
In the case where the homogeneous space is the Diffie-Hellman action this is the discrete log -/
def vectorization [principal_action_class G X] [fintype G] [decidable_eq X] (x y : X) : G :=
fintype.choose (λ g, g +ᵥ x = y) (principal_action_class.vectorization_unique x y)

variables [principal_action_class G X]
  [fintype G] [decidable_eq X]

@[simp]
lemma vectorization_apply (x y : X) :
  (vectorization G x y) +ᵥ x = y :=
fintype.choose_spec (λ g, g +ᵥ x = y) (principal_action_class.vectorization_unique x y)

variable {G}

@[simp]
lemma vectorization_vadd (x : X) (g : G) :
  vectorization G x (g +ᵥ x) = g :=
begin
  refine free_action_class.eq_of_vadd_eq x _,
  simp,
end

@[simp]
lemma eq_vectorization_iff (g : G) (x y : X) :
  g = vectorization G x y ↔ y = g +ᵥ x :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [h, vectorization_apply] },
  { rw [h, vectorization_vadd] }
end

lemma vadd_eq_vadd_iff_left (g g' : G) (x y : X) :
  g +ᵥ x = g' +ᵥ y ↔ g = g' + vectorization G x y :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw ← vectorization_apply G x y at h,
    rw vadd_vadd at h,
    refine free_action_class.eq_of_vadd_eq x h },
  { rw [h, ← vadd_vadd, vectorization_apply] }
end

lemma vectorization_swap (G : Type) {X : Type} [add_group G] [add_action G X]
  [principal_action_class G X] [fintype G] [decidable_eq X]
  (x y : X) : (vectorization G x y) = - (vectorization G y x) :=
begin
  refine free_action_class.eq_of_vadd_eq x _,
  simp [eq_neg_vadd_iff],
end

end vectorization

end action_classes