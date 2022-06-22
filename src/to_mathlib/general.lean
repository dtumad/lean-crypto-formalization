import measure_theory.probability_mass_function.basic
import data.vector.basic

open_locale nnreal ennreal classical

lemma pmf.apply_eq_one_iff {A : Type} (p : pmf A) (a : A) :
  p a = 1 ↔ p.support = {a} :=
begin
  sorry
end

lemma vector.not_mem_to_list_of_length_zero {A : Type} (v : vector A 0) (a : A) :
  a ∉ v.to_list :=
begin
  rw [vector.eq_nil v],
  exact id,
end

lemma vector.eq_cons_iff {A : Type} {n : ℕ} (v : vector A n.succ)
  (a : A) (as : vector A n) : v = a ::ᵥ as ↔ v.head = a ∧ v.tail = as :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [h, vector.head_cons, vector.tail_cons],
    exact ⟨rfl, rfl⟩ },
  { refine trans (vector.cons_head_tail v).symm _,
    rw [h.1, h.2] },
end

lemma vector.ne_cons_iff {A : Type} {n : ℕ} (v : vector A n.succ)
  (a : A) (as : vector A n) : v ≠ a ::ᵥ as ↔ v.head ≠ a ∨ v.tail ≠ as :=
by rw [ne.def, vector.eq_cons_iff v a as, not_and_distrib]

/-- TODO: generalize from `nnreal`-/
lemma tsum_tsum_eq_single {α β γ : Type*} [add_comm_monoid γ]
  [topological_space γ] [t2_space γ]
  (f : α → β → γ) (a : α) (b : β)
  (hf : ∀ (a' : α) (b' : β), a ≠ a' ∨ b ≠ b' → f a' b' = 0) :
  ∑' (a' : α) (b' : β), f a' b' = f a b :=
begin
  sorry
end