import computational_monads.simulation_semantics.constructions.logging.logging_oracle
import computational_monads.simulation_semantics.constructions.logging.query_log.lookup
import computational_monads.simulation_semantics.oracle_compose

open oracle_comp oracle_spec

variables {α β γ : Type} {spec : oracle_spec} [computable spec]

/-- Oracle for logging previous queries, and returning the same value for matching inputs -/
def caching_oracle (spec : oracle_spec) [spec.computable] :
  sim_oracle spec spec (query_log spec) :=
{ default_state := query_log.init spec,
  o := λ i ⟨t, log⟩, match log.lookup i t with
  | (some u) := return (u, log) -- Return the cached value if it already exists
  | none := do {u ← query i t, return (u, log.log_query i t u)}
  end }

namespace caching_oracle

variables (oa : oracle_comp spec α) (i : spec.ι) (t : spec.domain i) (u : spec.range i)
  (log : query_log spec) --naming → cache

@[simp] lemma apply_eq : (caching_oracle spec) i (t, log) = option.rec_on (log.lookup i t)
  (query i t >>= λ u, return (u, log.log_query i t u)) (λ u, return (u, log)) :=
by {simp only [caching_oracle, sim_oracle.has_coe_to_fun_def], induction log.lookup i t; refl }

lemma apply_eq_of_lookup_eq_none (hlog : log.lookup i t = none) :
  (caching_oracle spec) i (t, log) = (query i t >>= λ u, return (u, log.log_query i t u)) :=
by rw [apply_eq, hlog]

lemma apply_eq_of_lookup_eq_some (u : spec.range i) (hlog : log.lookup i t = some u) :
  (caching_oracle spec) i (t, log) = return (u, log) :=
by rw [apply_eq, hlog]

lemma apply_eq_of_not_queried (hlog : log.not_queried i t) :
  (caching_oracle spec) i (t, log) = (query i t >>= λ u, return (u, log.log_query i t u)) :=
by rw [apply_eq, (query_log.lookup_eq_none_iff_not_queried _ _ _).2 hlog]

section support

@[simp] lemma support_apply : ((caching_oracle spec) i (t, log)).support = if log.not_queried i t
  then {x | x.2 = log.log_query i t x.1} else {x | some x.1 = log.lookup i t ∧ x.2 = log} :=
begin
  split_ifs with hlog; ext x,
  { rw [apply_eq_of_not_queried i t log hlog, support_bind_return, support_query,
      set.top_eq_univ, set.image_univ, set.mem_range, set.mem_set_of_eq],
    refine ⟨λ h, _, λ h, _⟩,
    { obtain ⟨u, rfl⟩ := h,
      refl },
    { exact ⟨x.1, h ▸ (prod.eq_iff_fst_eq_snd_eq.2 ⟨rfl, rfl⟩)⟩ } },
  { obtain ⟨u, hu⟩ := log.exists_eq_lookup_of_not_not_queried i t hlog,
    simp only [apply_eq_of_lookup_eq_some _ _ _ u hu.symm, ← hu, support_return,
      prod.eq_iff_fst_eq_snd_eq, set.mem_singleton_iff, set.mem_set_of_eq] }
end

lemma support_apply_of_not_queried (hlog : log.not_queried i t) :
  ((caching_oracle spec) i (t, log)).support = {x | x.2 = log.log_query i t x.1} :=
by rw [support_apply, if_pos hlog]

lemma support_apply_of_not_not_queried (hlog : ¬ log.not_queried i t) :
  ((caching_oracle spec) i (t, log)).support = {x | some x.1 = log.lookup i t ∧ x.2 = log} :=
by rw [support_apply, if_neg hlog]

/-- If the initial cache has `nodup` for some oracle, then so does the final cache. -/
lemma nodup_simulate (hlog : (log i).nodup) (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support) : (x.2 i).nodup :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob j t,
  { rw [simulate_return, support_return, set.mem_singleton_iff] at hx,
    refine hx.symm ▸ hlog },
  {
    sorry,
  },
  { by_cases h : log.not_queried j t,
    { rw [simulate_query, support_apply, if_pos h, set.mem_set_of_eq] at hx,
      rw [hx, log.nodup_log_query_iff j t x.1 i hlog],
      refine or.inr ((log.not_queried_iff_not_mem _ _).1 h _) },
    { rw [simulate_query, support_apply, if_neg h, set.mem_set_of_eq] at hx,
      exact hx.2.symm ▸ hlog } }
end

/-- If a value is already cached in the initial state, it has the same cache value after. -/
lemma lookup_simulate_eq_some_of_lookup_eq_some (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support)
  (hlog : log.lookup i t = some u) : x.2.lookup i t = some u :=
begin
  sorry
end

/-- If a value isn't cached after simulation, it wasn't cached in the initial state. -/
lemma lookup_eq_none_of_lookup_simulate_eq_none (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support)
  (hx' : x.2.lookup i t = none) : log.lookup i t = none :=
begin
  sorry
end

/-- The length of the final cache is at least as long as the initial cache -/
lemma len_cache_le_len_cache_simulate (x : α × query_log spec)
  (hx : x ∈ (simulate (caching_oracle spec) oa log).support) :
  (log i).length ≤ (x.2 i).length :=
begin
  sorry
end

/-- For any query fresh to the initial cache, if there is some output such that query has a cached
value, then there are also outputs with any other possible cached value.  -/
lemma exists_log_lookup_eq_some (hlog : log.not_queried i t)
  (x : α × query_log spec) (hx : x ∈ (simulate (caching_oracle spec) oa log).support)
  (h : x.2.lookup i t = some u) (u' : spec.range i) :
  ∃ (y : α × query_log spec) (hy : y ∈ (simulate (caching_oracle spec) oa log).support),
    y.2.lookup i t = some u' :=
begin
  sorry
end

-- TODO: generalize. Should also work for log→seed probably ?
/-- Re-running a computation with an old cache doesn't change the possible outputs,
assuming the old cache was generated by an honest simulation. -/
theorem support_simulate_bind_simulate' (oa : oracle_comp spec α) :
  (simulate (caching_oracle spec) oa log >>=
    λ x, simulate (caching_oracle spec) oa x.2).support =
      (simulate (caching_oracle spec) oa log).support :=
begin
  induction oa using oracle_comp.induction_on with α a α β oa ob hoa hob i t,
  {
    simp only [simulate_return, support_bind_return, support_return, set.image_singleton],
  },
  {
    sorry,
  },
  {
    sorry,
  }
end

end support

section eval_dist


end eval_dist

end caching_oracle