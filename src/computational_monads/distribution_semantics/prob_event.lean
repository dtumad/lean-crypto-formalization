import computational_monads.distribution_semantics.eval_distribution

noncomputable theory

open oracle_comp oracle_spec
open_locale big_operators nnreal ennreal classical

variables {A B C : Type} {spec : oracle_spec} [h' : spec.finite_range]
include h'

/-- Probability of a predicate holding after running a particular experiment.
  Defined in terms of the outer measure associated to the corresponding `pmf` -/
noncomputable def prob_event (oa : oracle_comp spec A) (event : set A) :
  ℝ≥0∞ := ⟦oa⟧.to_outer_measure event

notation `⟦` event `|` oa `⟧` := prob_event oa event

/-- Probability that the result of a computation is greater than `5` -/
noncomputable example (oa : oracle_comp coin_oracle (fin 10)) :
  ℝ≥0∞ := ⟦ (>) 5 | oa ⟧

@[simp]
lemma eval_prob_eq_zero_iff_disjoint_support (oa : oracle_comp spec A) (event : set A) :
  ⟦ event | oa ⟧ = 0 ↔ disjoint oa.support event :=
by simp only [prob_event, pmf.to_outer_measure_apply_eq_zero_iff, support_eval_distribution]

@[simp]
lemma eval_prob_eq_one_iff_support_subset (oa : oracle_comp spec A) (event : set A) :
  ⟦ event | oa ⟧ = 1 ↔ oa.support ⊆ event :=
by simp only [prob_event, pmf.to_outer_measure_apply_eq_one_iff, support_eval_distribution]

@[simp]
lemma eval_prob_return (a : A) (event : set A) :
  ⟦ event | (return a : oracle_comp spec A) ⟧ = if a ∈ event then 1 else 0 :=
pmf.to_outer_measure_pure_apply a event

lemma eval_prob_return_of_true (a : A) (event : set A) (ha : a ∈ event) :
  ⟦ event | (return a : oracle_comp spec A) ⟧ = 1 :=
by simp only [ha, eval_prob_return, if_true]

lemma eval_prob_return_of_false (a : A) (event : set A) (ha : a ∉ event) :
  ⟦ event | (return a : oracle_comp spec A) ⟧ = 0 :=
by simp only [ha, eval_prob_return, if_false]

@[simp]
lemma eval_prob_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (event : set B) :
  ⟦ event | oa >>= ob ⟧ = ∑' (a : A), ⟦oa⟧ a * ⟦ event | ob a ⟧ :=
begin
  simp only [prob_event, eval_distribution_bind],
  refine pmf.to_outer_measure_bind_apply ⟦oa⟧ (λ a, ⟦ob a⟧) event,
end

@[simp]
lemma eval_prob_pure_bind (a : A) (ob : A → oracle_comp spec B) (event : set B) :
  ⟦ event | return a >>= ob ⟧ = ⟦ event | ob a ⟧ :=
begin
  simp only [eval_prob_bind, eval_distribution_return, pmf.pure_apply],
  refine trans (tsum_congr $ λ a', _) (tsum_ite_eq a ⟦ event | ob a⟧),
  split_ifs with h; simp [h],
end

@[simp]
lemma eval_prob_query (i : spec.ι) (t : spec.domain i) (event : set $ spec.range i) :
  ⟦ event | query i t ⟧ = fintype.card event / fintype.card (spec.range i) :=
pmf.to_outer_measure_uniform_of_fintype_apply event

lemma eval_prob_prod_eq (oa : oracle_comp spec (A × A)) :
  ⟦ λ ⟨a, a'⟩, a = a' | oa ⟧ = ∑' (a₀ : A), ⟦ λ ⟨a, a'⟩, a = a₀ ∧ a' = a₀ | oa⟧ :=
begin
  simp,
  sorry
end
