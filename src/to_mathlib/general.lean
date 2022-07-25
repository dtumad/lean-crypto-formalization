import measure_theory.probability_mass_function.constructions 
import data.vector.basic

/-! 
# Misc Lemmas That Ideally Should Port to Mathlib
-/

open_locale nnreal ennreal classical big_operators


instance set.diagonal.decidable_pred {α : Type*} [h : decidable_eq α] :
  decidable_pred (set.diagonal α) := λ x, h x.1 x.2

lemma tsum_pow_two_ge_pow_two_tsum {α : Type*} [fintype α] [topological_space ℝ≥0∞]
  (f : α → ℝ≥0∞) :
  ∑' (a : α), (f a) ^ 2 ≥ (∑' (a : α), f a) ^ 2 / fintype.card α :=
sorry

lemma vector.to_list_nonempty {α : Type} {n : ℕ} (v : vector α (n + 1)) : ¬ v.to_list.empty :=
match v with
| ⟨a :: as, _⟩ := by simp
end

lemma finset.to_list_nonempty {A : Type} (s : finset A) (hs : s.nonempty) : ¬ s.to_list.empty :=
let ⟨x, hx⟩ := hs in
  λ h', list.not_mem_nil x ((list.empty_iff_eq_nil.1 h') ▸ (finset.mem_to_list s).2 hx)

lemma list.drop_succ_cons {A : Type} (as : list A) (a : A) (n : ℕ) :
  (a :: as).drop (n + 1) = as.drop n :=
rfl

lemma vector.not_mem_of_length_zero {A : Type} (v : vector A 0) (a : A) :
  a ∉ v.to_list :=
(vector.eq_nil v).symm ▸ id

lemma vector.eq_cons_iff {A : Type} {n : ℕ} (v : vector A n.succ)
  (a : A) (as : vector A n) : v = a ::ᵥ as ↔ v.head = a ∧ v.tail = as :=
⟨λ h, h.symm ▸ ⟨vector.head_cons a as, vector.tail_cons a as⟩,
  λ h, trans (vector.cons_head_tail v).symm (by rw [h.1, h.2])⟩

lemma vector.ne_cons_iff {A : Type} {n : ℕ} (v : vector A n.succ)
  (a : A) (as : vector A n) : v ≠ a ::ᵥ as ↔ v.head ≠ a ∨ v.tail ≠ as :=
by rw [ne.def, vector.eq_cons_iff v a as, not_and_distrib]

lemma vector.mem_cons_iff {A : Type} {n : ℕ} (a : A) (as : vector A n)
  (a' : A) : a' ∈ (a ::ᵥ as).to_list ↔ a' = a ∨ a' ∈ as.to_list :=
by rw [vector.to_list_cons, list.mem_cons_iff]

lemma vector.head_mem {A : Type} {n : ℕ} (v : vector A n.succ) :
  v.head ∈ v.to_list :=
vector.mem_iff_nth.2 ⟨0, vector.nth_zero v⟩

lemma vector.mem_cons_self {A : Type} {n : ℕ} (a : A) (as : vector A n) :
  a ∈ (a ::ᵥ as).to_list :=
vector.mem_iff_nth.2 ⟨0, vector.nth_cons_zero a as⟩

lemma vector.mem_cons_of_mem {A : Type} {n : ℕ} (a : A) (as : vector A n)
  (a' : A) (ha' : a' ∈ as.to_list) : a' ∈ (a ::ᵥ as).to_list :=
(vector.mem_cons_iff a as a').2 (or.inr ha')

lemma vector.exists_eq_cons {A : Type} {n : ℕ} (v : vector A n.succ) :
  ∃ (a : A) (as : vector A n), v = a ::ᵥ as :=
⟨v.head, v.tail, (vector.eq_cons_iff v v.head v.tail).2 ⟨rfl, rfl⟩⟩

lemma vector.mem_of_mem_tail {A : Type} {n : ℕ} (a : A) (as : vector A n)
  (ha : a ∈ as.tail.to_list) : a ∈ as.to_list :=
begin
  induction n,
  { rw [vector.eq_nil as, vector.tail_nil] at ha,
    refine false.elim ha },
  { obtain ⟨a', as, h⟩ := vector.exists_eq_cons as,
    rw [h],
    refine vector.mem_cons_of_mem a' as _ _,
    rwa [h, vector.tail_cons] at ha }
end

section pmf

section apply_eq_one

lemma nnreal.sum_le_tsum {α : Type} {f : α → ℝ≥0} (hf : summable f) (s : finset α) :
  ∑ x in s, f x ≤ ∑' x, f x :=
by simpa only [← ennreal.coe_le_coe, ennreal.coe_tsum hf, ennreal.coe_finset_sum] 
  using ennreal.sum_le_tsum s

lemma pmf.apply_eq_one_iff {A : Type} (p : pmf A) (a : A) :
  p a = 1 ↔ p.support = {a} :=
begin
  refine ⟨λ h, set.eq_of_subset_of_subset _ _, λ h, le_antisymm (pmf.coe_le_one p a) (le_of_eq _)⟩,
  { refine λ a' ha', by_contradiction (λ h', false.elim (ne_of_gt _ p.tsum_coe)),
    have : a ∉ {a'} := finset.not_mem_singleton.2 (ne.symm h'),
    calc 1 < p a + p a' : lt_add_of_le_of_pos (le_of_eq h.symm)
        (lt_of_le_of_ne (nnreal.coe_nonneg $ p a') (ha'.symm))
      ... ≤ ∑ x in {a, a'}, p x : by rw [finset.sum_insert this, finset.sum_singleton]
      ... ≤ ∑' (x : A), p x : nnreal.sum_le_tsum p.summable_coe {a, a'} },
  { intros a' ha',
    rw [set.mem_singleton_iff.1 ha', pmf.mem_support_iff, h],
    exact one_ne_zero },
  { refine trans (p.tsum_coe).symm (trans (tsum_congr $ λ a', _) (tsum_ite_eq a _)),
    split_ifs with haa',
    { rw haa' },
    { rwa [pmf.apply_eq_zero_iff p, h, set.mem_singleton_iff] } }
end

end apply_eq_one

@[simp]
lemma pmf.map_bind' {A B C : Type} (p : pmf A) (q : A → pmf B) (f : B → C) :
  (p >>= q).map f = p >>= (λ a, (q a).map f) :=
sorry

@[simp]
lemma pmf.map_bind {A B C : Type} (p : pmf A) (q : A → pmf B) (f : B → C) :
  f <$> (p >>= q) = p >>= λ a, (f <$> (q a)) :=
begin
  refine (pmf.map_bind' p q f),
end

@[simp]
lemma pmf.bind_const {A B : Type} (p : pmf A) (q : pmf B) :
  (p >>= λ _, q) = q :=
begin
  ext x,
  simp [has_bind.bind, (nnreal.tsum_mul_right _ (q x))]
end


end pmf