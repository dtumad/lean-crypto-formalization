import measure_theory.probability_mass_function.basic
import data.vector.basic

-- Misc. lemmas that should eventually be moved into actual mathlib -

open_locale nnreal ennreal classical

lemma finset.to_list_nonempty {A : Type} (s : finset A) (hs : s.nonempty) : ¬ s.to_list.empty :=
let ⟨x, hx⟩ := hs in
  λ h', list.not_mem_nil x ((list.empty_iff_eq_nil.1 h') ▸ (finset.mem_to_list s).2 hx)

lemma pmf.apply_eq_one_iff {A : Type} (p : pmf A) (a : A) :
  p a = 1 ↔ p.support = {a} :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    refine set.eq_of_subset_of_subset _ _,
    {
      intros a' ha',
      rw [set.mem_singleton_iff],
      rw [pmf.mem_support_iff] at ha',
      sorry
    },
    {
      intros a' ha',
      have : a' = a := ha',
      rw [this, pmf.mem_support_iff],
      exact λ ha, one_ne_zero (trans h.symm ha),
    }
  },
  {
    refine le_antisymm _ _,
    {
      refine pmf.coe_le_one p a,
    },
    {
      sorry
    }
  }
end

lemma vector.not_mem_of_length_zero {A : Type} (v : vector A 0) (a : A) :
  a ∉ v.to_list :=
(vector.eq_nil v).symm ▸ id

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
  [topological_space γ] [t2_space γ] (f : α → β → γ) (a : α) (b : β)
  (hf : ∀ (a' : α) (b' : β), a ≠ a' ∨ b ≠ b' → f a' b' = 0) :
  ∑' (a' : α) (b' : β), f a' b' = f a b :=
(tsum_eq_single a $ λ a' ha', (tsum_eq_single b $ λ b' hb', hf a' b' (or.inl ha'.symm)).trans
  (hf a' b (or.inl ha'.symm))).trans (tsum_eq_single b (λ b' hb', hf a b' (or.inr hb'.symm)))