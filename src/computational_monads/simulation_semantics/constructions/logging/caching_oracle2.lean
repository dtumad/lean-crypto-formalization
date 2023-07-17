/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.simulation_semantics.query_cache.get_or_else
import computational_monads.simulation_semantics.query_cache.add_fresh_queries
import computational_monads.simulation_semantics.query_cache.sdiff
import computational_monads.simulation_semantics.simulate.monad
import computational_monads.simulation_semantics.simulate.query
import computational_monads.distribution_semantics.prod
import computational_monads.constructions.product

/-!
# Caching Simulation Oracle

This file defines a `sim_oracle` that implements caching functionality.
`cachingₛₒ` represents a simulator that caches fresh queries and returns the same value
for any future queries, using a `query_cache` as an internal state for tracking this.

This is used by being composed with other oracles, such as in `random_oracle`.

-- TODO: implicit parameters here (and other cache files)
-/

open oracle_comp oracle_spec query_cache
open prod (fst) (snd)
open_locale ennreal big_operators classical -- TODO: temp classical (maybe we should have this for all dist sem)

variables {α β γ δ : Type} {spec spec' : oracle_spec}

/-- Oracle for tracking previous queries, and returning the same value for matching inputs.
The `query_cache.get_or_else` function allows us to run a fallback for non-cached values. -/
def cachingₛₒ {spec : oracle_spec} : sim_oracle spec spec (query_cache spec) :=
{ default_state := ∅,
  o := λ i ⟨t, cache⟩, cache.get_or_else i t (query i t) }

namespace cachingₛₒ

section apply

@[simp] lemma apply_eq (i : spec.ι) (z : spec.domain i × query_cache spec) :
  cachingₛₒ i z = z.2.get_or_else i z.1 (query i z.1) := by cases z; refl

variables {i : spec.ι} {z : spec.domain i × query_cache spec}
  {t : spec.domain i} {s₀ : query_cache spec}

lemma apply_eq_of_is_fresh (h : z.2.is_fresh i z.1) :
  cachingₛₒ i z = query i z.1 >>= λ u, return (u, [i, z.1 ↦ u; z.2]) := by simp [h]

lemma apply_eq_of_is_fresh' (h : s₀.is_fresh i t) :
  cachingₛₒ i (t, s₀) = query i t >>= λ u, return (u, [i, t ↦ u; s₀]) := apply_eq_of_is_fresh h

lemma apply_eq_of_is_cached (h : z.2.is_cached i z.1) :
  cachingₛₒ i z = return ((z.2.lookup i z.1).get_or_else default, z.2) := by simp [h]

lemma apply_eq_of_is_cached' (h : s₀.is_cached i t) :
  cachingₛₒ i (t, s₀) = return ((s₀.lookup i t).get_or_else default, s₀) := apply_eq_of_is_cached h

lemma apply_eq_of_lookup_eq_some {u} (h : s₀.lookup i t = some u) :
  cachingₛₒ i (t, s₀) = return (u, s₀) := get_or_else_of_lookup_eq_some _ _ h

end apply

variables (oa : oracle_comp spec α)
  (s₀ s : query_cache spec)

section support

/-- Simulation with a caching oracle will only ever grow the cash and doesn't remove elements. -/
lemma le_of_mem_support_simulate {oa : oracle_comp spec α} {s₀ : query_cache spec} :
  ∀ z ∈ (simulate cachingₛₒ oa s₀).support, s₀ ≤ snd z :=
begin
  intros z hz,
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing s₀,
  { rw [mem_support_simulate_return_iff] at hz,
    exact hz.2 ▸ le_rfl },
  { rw [mem_support_simulate_bind_iff] at hz,
    obtain ⟨x, s, hs, hzx⟩ := hz,
    exact (hoa (x, s) hs).trans (hob x z hzx) },
  { exact s₀.le_of_mem_support_get_or_else z hz }
end

/-- The output of two simulations of a computation using `cachingₛₒ` differ iff there is some
query made in both simulations for which the query response differs.
In particular it they can't differ simply by having some additional values being fresh. -/
lemma ne_iff_exists_lookup_ne_of_mem_support_simulate {oa : oracle_comp spec α}
  {s₀ : query_cache spec} {z z' : α × query_cache spec}
  (hz : z ∈ (simulate cachingₛₒ oa s₀).support) (hz' : z' ∈ (simulate cachingₛₒ oa s₀).support) :
  z ≠ z' ↔ ∃ i t, z.2.is_cached i t ∧ z'.2.is_cached i t ∧ z.2.lookup i t ≠ z'.2.lookup i t :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { induction oa using oracle_comp.induction_on
      with α a α β oa ob hoa hob i t generalizing s₀,
    { simp only [support_simulate_return, set.mem_singleton_iff] at hz hz',
      exact (h (hz.trans hz'.symm)).elim },
    { rw [mem_support_simulate_bind_iff'] at hz hz',
      obtain ⟨x, hx, hxz⟩ := hz,
      obtain ⟨x', hx', hxz'⟩ := hz',
      by_cases hxx' : x = x',
      { exact hob x.1 h hxz (hxx'.symm ▸ hxz') },
      { obtain ⟨i, t, htx, htx', ht⟩ := hoa hxx' hx hx',
        have hz : x.2 ≤ z.2 := le_of_mem_support_simulate z hxz,
        have hz' : x'.2 ≤ z'.2 := le_of_mem_support_simulate z' hxz',
        refine ⟨i, t, is_cached_of_le_of_is_cached hz htx,
          is_cached_of_le_of_is_cached hz' htx', _⟩,
        rwa [lookup_eq_lookup_of_le_of_is_cached hz htx,
          lookup_eq_lookup_of_le_of_is_cached hz' htx'] } },
    { by_cases hs₀ : s₀.is_fresh i t,
      { simp only [simulate_query, hs₀, apply_eq, get_or_else_of_is_fresh, support_bind_return,
          support_query, set.image_univ, set.mem_range] at hz hz',
        obtain ⟨u, rfl⟩ := hz,
        obtain ⟨u', rfl⟩ := hz',
        refine ⟨i, t, _⟩,
        simp only [is_cached_cache_query_same_input, true_and,
          lookup_cache_query_same_input, ne.def, option.some_inj],
        simpa only [ne.def, prod.eq_iff_fst_eq_snd_eq, not_and_distrib,
          cache_query_eq_cache_query_iff_of_same_cache, or_self] using h },
      { rw [not_is_fresh_iff_is_cached] at hs₀,
        simp [simulate_query, hs₀] at hz hz',
        refine (h (hz.trans hz'.symm)).elim } } },
  { exact let ⟨i, t, hzt, hzt', hz⟩ := h in λ h',
      (query_cache.ne_of_lookup_ne _ _ i t hz) (prod.eq_iff_fst_eq_snd_eq.1 h').2 }
end

/-- Given a possible result `z` of simulating a computation `oa >>= ob` with a caching oracle,
we get a stronger version `mem_support_simulate_bind_iff` that includes uniqueness of the
intermediate result (since all choices made must align with the cached values in `z`).  -/
theorem mem_support_simulate_bind_iff (ob : α → oracle_comp spec β)
  (z : β × query_cache spec) : z ∈ (simulate cachingₛₒ (oa >>= ob) s₀).support ↔
    ∃! (y : α × query_cache spec), y ∈ (simulate cachingₛₒ oa s₀).support ∧
      z ∈ (simulate cachingₛₒ (ob y.1) y.2).support :=
begin
  rw [mem_support_simulate_bind_iff'],
  refine ⟨λ h, exists_unique_of_exists_of_unique h _, λ h, exists_of_exists_unique h⟩,
  rintros y y' ⟨hy, hyz⟩ ⟨hy', hyz'⟩,
  by_contradiction h,
  obtain ⟨i, t, hty, hty', ht⟩ := (ne_iff_exists_lookup_ne_of_mem_support_simulate hy hy').1 h,
  rwa [← lookup_eq_lookup_of_le_of_is_cached (le_of_mem_support_simulate _ hyz) hty,
    ← lookup_eq_lookup_of_le_of_is_cached (le_of_mem_support_simulate _ hyz') hty',
    ne.def, eq_self_iff_true, not_true] at ht,
end

lemma cached_inputs_diff_antitone (s₀) {s s' : query_cache spec}
  (hs : s ≤ s') : (s₀ \ s').cached_inputs ⊆ (s₀ \ s).cached_inputs :=
begin
  sorry
end

-- TODO: why not just use "empty" naming instead of init
lemma eq_init_of_le_of_le_diff {s₀ s s' : query_cache spec}
  (hs : s₀ ≤ s) (hs' : s₀ ≤ s' \ s) : s₀ = ∅ :=
begin
  refine eq_bot_iff.2 (λ i t u hu, _),
  specialize hs i t u hu,
  have : ¬ s.is_fresh i t := not_is_fresh_of_lookup_eq_some hs,
  specialize hs' i t u hu,
  simp [this, lookup_sdiff] at hs',
  refine hs'.elim,
end

theorem mem_support_simulate_iff_of_le (oa : oracle_comp spec α) {s₀ s₁ : query_cache spec}
  (hs : s₀ ≤ s₁) (z : α × query_cache spec) :
  z ∈ (simulate cachingₛₒ oa s₁).support ↔
  (z.1, s₀.add_fresh_queries (z.2 \ s₁)) ∈ (simulate cachingₛₒ oa s₀).support :=
begin
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing s₀ s₁,
  {
    refine ⟨λ h, _, λ h, _⟩,
    {
      rw [mem_support_simulate_return_iff] at h,
      simp [h.1, h.2],
    },
    {
      simp [mem_support_simulate_return_iff] at h,
      simp [prod.eq_iff_fst_eq_snd_eq, h.1],
      have := (cached_inputs_diff_antitone z.2 hs),
      sorry,
    }
  },
  {
    sorry,
  },
  {
    sorry
  }
end

theorem exists_unique_state_mem_support_of_le (oa : oracle_comp spec α) {s₀ s₁ : query_cache spec}
  (hs : s₀ ≤ s₁) (z : α × query_cache spec) (hz : z ∈ (simulate cachingₛₒ oa s₁).support) :
  ∃! (s : query_cache spec), s ≤ z.2 ∧ (z.1, s) ∈ (simulate cachingₛₒ oa s₀).support :=
begin
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing s₀ s₁,
  { rw [support_simulate_return, set.mem_singleton_iff, prod.eq_iff_fst_eq_snd_eq] at hz,
    suffices : ∃! (s : query_cache spec), s ≤ s₁ ∧ s = s₀,
    by simpa [hz.1, hz.2] using this,
    exact ⟨s₀, ⟨hs, rfl⟩, λ s hs, hs.2⟩ },
  {
    refine exists_unique_of_exists_of_unique _ _,
    {
      rw [mem_support_simulate_bind_iff'] at hz,
      obtain ⟨y, hy, hyz⟩ := hz,
      specialize hoa y hs hy,
      obtain ⟨s₁', hs₁'⟩ := exists_of_exists_unique hoa,
      sorry,
    },
    {
      sorry,
    }
    -- rw [mem_support_simulate_bind_iff'] at hz,
    -- obtain ⟨x, hx, hzx⟩ := hz,
    -- specialize hoa _ hs hx,
    -- obtain ⟨s', hs', hsz'⟩ := hoa,
    -- specialize hob x.1 z hs'.1 hzx,
    -- obtain ⟨s₁', hs₁', hzs₁'⟩ := hob,
    -- refine ⟨s₁', ⟨hs₁'.1, _⟩, _⟩,
    -- {
    --   rw [mem_support_simulate_bind_iff'],
    --   refine ⟨⟨x.1, s'⟩, hs'.2, hs₁'.2⟩,
    -- },
    -- {
    --   intros sb hsb,
    --   rw [mem_support_simulate_bind_iff'] at hsb,
    --   obtain ⟨hsbz, ⟨x'', hx''⟩⟩ := hsb,
    --   refine hzs₁' _ ⟨hsbz, _⟩,
    --   have : x'' = (x.1, s') := sorry,
    -- }
  },
  {
    by_cases hs₁ : s₁.is_fresh i t,
    {
      have hs₀ : s₀.is_fresh i t := is_fresh_of_le_of_is_fresh hs hs₁,
      simp only [hs₀, hs₁, support_simulate_query, apply_eq, get_or_else_of_is_fresh,
        support_bind_return, support_query, set.image_univ, set.mem_range,
          prod.mk.inj_iff, exists_eq_left] at hz ⊢,
      obtain ⟨x, rfl⟩ := hz,
      exact ⟨[i, t ↦ x; s₀], ⟨(cache_query_le_cache_query_iff_of_is_fresh x hs₀ hs₁).2 hs, rfl⟩,
        λ s hs, by rw [← hs.2]⟩ },
    {
      rw [not_is_fresh_iff_exists_lookup_eq_some] at hs₁,
      obtain ⟨u, hu⟩ := hs₁,
      refine ⟨[i, t ↦ u; s₀], ⟨_, _⟩, _⟩,
      {
        refine trans _ (le_of_mem_support_simulate z hz),
        rwa [cache_query_le_iff_of_le hs],
      },
      {
        rw [simulate_query, apply_eq_of_lookup_eq_some hu, mem_support_return_iff] at hz,
        simp only [hz, support_simulate_query, apply_eq],
        by_cases hs₀ : s₀.is_fresh i t,
        {
          simp only [support_get_or_else_of_is_fresh _ _ hs₀, support_query, set.image_univ,
            set.mem_range, prod.mk.inj_iff, exists_eq_left],
        },
        {

          rw [not_is_fresh_iff_is_cached] at hs₀,
          simp [support_get_or_else_of_is_cached _ _ hs₀, (lookup_eq_lookup_of_le_of_is_cached hs hs₀).symm.trans hu],
        }
      },
      {
        rintro s ⟨hs, hsz⟩,
        rw [simulate_query, apply_eq_of_lookup_eq_some hu, mem_support_return_iff,
            prod.eq_iff_fst_eq_snd_eq] at hz,
        by_cases hs₀ : s₀.is_fresh i t,
        {
          simp [simulate_query, hs₀, hz.1] at hsz,
          exact hsz.symm
        },
        {
          rw [not_is_fresh_iff_is_cached] at hs₀,
          simp [simulate_query, hs₀, hz.1] at hsz,
          rw [hsz.2, eq_comm, cache_query_eq_self_iff, hsz.1],
          rw [is_cached_iff_exists_lookup_eq_some] at hs₀,
          obtain ⟨u', hu'⟩ := hs₀,
          rw [hu', option.get_or_else_some],
        }
      }
    }
  }
end

/-- The possible outputs of simulating a computation with a larger initial cache is
at most the original set of possible outputs (although the possible final caches may differ). -/
lemma support_antitone (oa : oracle_comp spec α) {s₀ s : query_cache spec}
  (hs : s₀ ≤ s) : (simulate' cachingₛₒ oa s).support ⊆ (simulate' cachingₛₒ oa s₀).support :=
begin

  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing s₀ s,
  { simp only [support_simulate', support_simulate_return, set.image_singleton] },
  {
    intros y hy,
    simp_rw [mem_support_simulate'_iff_exists_state,
      cachingₛₒ.mem_support_simulate_bind_iff] at hy,

    obtain ⟨s₁, hx⟩ := hy,
    obtain ⟨x, hxy⟩ := exists_of_exists_unique hx,


    rw [mem_support_simulate'_bind_iff],
    refine ⟨x.1, x.2, _⟩,
    sorry,

    -- specialize hoa hs hxy.1,

    -- have hx' : x.1 ∈ (simulate' cachingₛₒ oa s).support := sorry,
    -- specialize hoa hs hx',
    -- rw [mem_support_simulate'_iff_exists_state] at hoa,
    -- obtain ⟨sx, hsx⟩ := hoa,
    -- have : sx = x.2 := begin
    --   suffices : (x.1, sx) = x,
    --   from (prod.eq_iff_fst_eq_snd_eq.1 this).2,
    -- end,
    -- refine ⟨this ▸ hsx, _⟩,



    -- rw [mem_support_simulate'_bind_iff] at hy ⊢,
    -- obtain ⟨x, s', hx, hy⟩ := hy,
    -- have hs' : s ≤ s' := le_of_mem_support_simulate _ hx,
    -- specialize hob x hs' hy,
    -- refine ⟨x, s, _, hob⟩,
    -- rw [mem_support_simulate'_iff_exists_state] at hy,
    -- obtain ⟨sy, hsy⟩ := hy,
    -- have hx' : x ∈ (simulate' cachingₛₒ oa s).support :=
    --   (mem_support_simulate'_iff_exists_state _ _ _ _).2 ⟨s', hx⟩,
    -- refine ⟨x, s, _⟩,
    -- specialize hob x _ hy,



    -- specialize hoa hs hx',
    -- rw [mem_support_simulate'_iff_exists_state] at hoa,
    -- obtain ⟨s'', hs''⟩ := hoa,
    -- refine ⟨x, s', _, _⟩,
    -- refine hob x _ hz,

    -- specialize hob x,
    -- have := le_of_mem_support_simulate _ hx,
    -- specialize hoa this,
    -- specialize hoa hs hx',
    -- specialize hob x this,
    -- refine ⟨x, s', _, _⟩,

  },
  { intros u hu,
    rw [mem_support_simulate'_query_iff] at hu ⊢,
    obtain ⟨s', hs'⟩ := hu,
    by_cases hs₀ : s₀.is_fresh i t,
    { simp_rw [apply_eq_of_is_fresh' hs₀, mem_support_query_bind_return_iff,
        prod.mk.inj_iff, exists_eq_left, exists_eq'] },
    { rw [not_is_fresh_iff_is_cached] at hs₀,
      simp only [apply_eq_of_is_cached' hs₀, mem_support_return_iff, prod.eq_iff_fst_eq_snd_eq,
        apply_eq_of_is_cached' (is_cached_of_le_of_is_cached hs hs₀), exists_eq_right,
        ← lookup_eq_lookup_of_le_of_is_cached hs hs₀] at ⊢ hs',
      exact hs'.1 } },
end

end support

lemma prob_output_simulate_bind_of_mem_support (ob : α → oracle_comp spec β)
  {z : β × query_cache spec} {y : α × query_cache spec}
  (hy : y ∈ (simulate cachingₛₒ oa s₀).support)
  (hz : z ∈ (simulate cachingₛₒ (ob y.1) y.2).support) :
  ⁅= z | simulate cachingₛₒ (oa >>= ob) s₀⁆ =
    ⁅= y | simulate cachingₛₒ oa s₀⁆ * ⁅= z | simulate cachingₛₒ (ob y.1) y.2⁆ :=
begin
  have : z ∈ (simulate cachingₛₒ (oa >>= ob) s₀).support,
  from (mem_support_simulate_bind_iff' _ _ _ _ _).2 ⟨y, hy, hz⟩,
  rw [simulate_bind, prob_output_bind_eq_tsum],
  refine tsum_eq_single y (λ y' hy', by_contra (λ h, hy' (unique_of_exists_unique
    ((cachingₛₒ.mem_support_simulate_bind_iff _ _ _ _).1 this) _ ⟨hy, hz⟩))),
  simpa only [← prob_output_ne_zero_iff, ne.def, ← not_or_distrib, ← mul_eq_zero] using h,
end

section extra_cache_choices

def extra_cache_choices (s₀ s : query_cache spec) : ℕ :=
(∏ i in (s \ s₀).cached_inputs, (fintype.card $ spec.range i.1))

@[simp] lemma extra_cache_choices_self : extra_cache_choices s₀ s₀ = 1 :=
by simp [extra_cache_choices]

lemma extra_cache_choices_mul_trans (s₀ s₁ s : query_cache spec) :
  extra_cache_choices s₀ s₁ * extra_cache_choices s₁ s = extra_cache_choices s₀ s :=
begin
  simp [extra_cache_choices],
  sorry,
end

@[simp] lemma extra_cache_choices_cache_query (i t u) (s : query_cache spec) :
  extra_cache_choices s [i, t ↦ u; s] = if s.is_fresh i t then fintype.card (spec.range i) else 1 :=
by split_ifs with h; simp [extra_cache_choices, sdiff_cache_query, h]

end extra_cache_choices

/-- Probability of getting to a final result given a partial cache for queries is given by
the product of probabilities that each additional query gets the expected result.
Note that this requires `z` be in the support of the simulation (as the empty product is `1`). -/
theorem finite_version (oa : oracle_comp spec α) (s₀ : query_cache spec)
  (z : α × query_cache spec) (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  ⁅= z | simulate cachingₛₒ oa s₀⁆ = (extra_cache_choices s₀ z.2)⁻¹ :=
begin
  -- have hs₀ : s₀ ≤ z.2 := le_of_mem_support_simulate z hz,
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing s₀,
  {
    simp only [support_simulate_return, set.mem_singleton_iff] at hz,
    simp only [hz, prob_output_simulate_return, eq_self_iff_true, if_true,
      extra_cache_choices_self, algebra_map.coe_one, inv_one],
  },
  {
    rw [cachingₛₒ.mem_support_simulate_bind_iff] at hz,
    obtain ⟨y, hy, hyz⟩ := exists_of_exists_unique hz,
    rw [prob_output_simulate_bind_of_mem_support _ _ _ hy hyz, hoa y s₀ hy, hob y.1 z y.2 hyz,
      ← ennreal.mul_inv (or.inr (ennreal.nat_ne_top _)) ((or.inl (ennreal.nat_ne_top _))),
      ← nat.cast_mul, extra_cache_choices_mul_trans],
  },
  {
    simp only [simulate_query, apply_eq] at hz ⊢,
    by_cases hs₀ : s₀.is_fresh i t,
    {
      simp only [get_or_else_of_is_fresh _ _ hs₀, support_bind_return, support_query,
        set.image_univ, set.mem_range] at hz,
      obtain ⟨u, rfl⟩ := hz,
      simp only [hs₀, get_or_else_of_is_fresh, extra_cache_choices_cache_query, if_true],
      refine trans (prob_output_bind_return_eq_single _ _ _ u _) (prob_output_query_eq_inv _ _ _),
      refine set.ext (λ u', _),
      simp [cache_query_eq_cache_query_iff_of_same_cache],
    },
    {
      rw [not_is_fresh_iff_is_cached] at hs₀,
      simp only [hs₀, get_or_else_of_is_cached, support_return, set.mem_singleton_iff] at hz,
      simp only [hz, extra_cache_choices_self, nat.cast_one, inv_one,
        get_or_else_of_is_cached _ _ hs₀],
      refine prob_output_return_self _ _,
    }
  }
end


lemma mem_support_of_le_mem_support (oa : oracle_comp spec α) {s₀ s : query_cache spec}
  (hs : s₀ ≤ s) (z : α × query_cache spec) (hzs : s ≤ z.2)
  (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  z ∈ (simulate cachingₛₒ oa s).support :=
begin
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing,
  {
    -- rw [simulate_return, simulate_return],
    simp at hz,
    simp [hz, prod.eq_iff_fst_eq_snd_eq] at hzs ⊢,
    refine le_antisymm hs hzs,
  },
  {
    sorry,
  },
  {
    simp [simulate_query] at hz ⊢,
    -- TODO: helper lemma
    by_cases hs₀ : s₀.is_fresh i t,
    {
      rw [mem_support_get_or_else_iff_of_is_fresh _ _ hs₀] at hz,
      rw [← hz.2] at hzs,
      sorry,
    },
    sorry,
  }
end

/-- Given a pair of caches `s ≤ s'`, such that some result `z` is possible in both simulations,
the probability of getting that result is higher when starting with the larger cache,
since it has fewer additional choices at which it could diverge from calculating `z`. -/
lemma prob_output_monotone (oa : oracle_comp spec α) (s s' : query_cache spec)
  (hs : s ≤ s') (z : α × query_cache spec)
  (hz' : z ∈ (simulate cachingₛₒ oa s').support) :
  ⁅= z | simulate cachingₛₒ oa s⁆ ≤ ⁅= z | simulate cachingₛₒ oa s'⁆ :=
begin
  by_cases hz : z ∈ (simulate cachingₛₒ oa s).support,
  {
    rw [finite_version _ _ _ hz', finite_version _ _ _ hz],
    sorry,
  },
  {
    simp only [hz, prob_output_eq_zero, not_false_iff, zero_le'],
  }
end

lemma prob_output_monotone_extra (oa : oracle_comp spec α) {s₀ s : query_cache spec}
  (hs : s₀ ≤ s) (z : α × query_cache spec) (hzs : s ≤ z.2)
  (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  ⁅= z | simulate cachingₛₒ oa s₀⁆ =
    ⁅= z | simulate cachingₛₒ oa s⁆ / (extra_cache_choices s₀ s) :=
begin
  have hz' : z ∈ (simulate cachingₛₒ oa s).support,
  from mem_support_of_le_mem_support oa hs z hzs hz,
  rw [finite_version _ _ _ hz', finite_version _ _ _ hz],
  have : z.snd.cached_inputs \ s₀.cached_inputs =
    (z.2.cached_inputs \ s.cached_inputs) ∪ (s.cached_inputs \ s₀.cached_inputs) := sorry,
  simp only [extra_cache_choices, this],
  sorry,
  -- rw [finset.prod_union sorry],
  -- simp only [finset.prod_union sorry, div_eq_mul_inv, nat.cast_mul],
  -- rw [ennreal.mul_inv sorry sorry],
end

-- lemma prob_output_monotone_extra_min (oa : oracle_comp spec α) (s s' : query_cache spec)
--   (hs : s ≤ s') (z : α × query_cache spec)
--   (hz' : z ∈ (simulate cachingₛₒ oa s').support) :
--   ⁅= z | simulate cachingₛₒ oa s⁆ ≤
--     ⁅= z | simulate cachingₛₒ oa s'⁆ / (s'.cached_inputs \ s.cached_inputs).card :=
-- begin
--   sorry
-- end

/-- A `forking_map` for a computation `oa` and initial state `s₀` is one that is well behaved
for forking a computation, via mapping output of simulation to a new initial state for running
the computation again. Requires that the mapping stays between the initial and final cache. -/
@[ext] structure forking_map (oa : oracle_comp spec α) (s₀ : query_cache spec) :=
(to_fun : α × query_cache spec → query_cache spec)
(le_to_fun : ∀ z ∈ (simulate cachingₛₒ oa s₀).support, s₀ ≤ to_fun z)
(to_fun_le : ∀ z ∈ (simulate cachingₛₒ oa s₀).support, to_fun z ≤ z.2)

namespace forking_map

instance fun_like (oa : oracle_comp spec α) (s₀ : query_cache spec) :
  fun_like (forking_map oa s₀) (α × query_cache spec) (λ z, query_cache spec) :=
{ coe := forking_map.to_fun,
  coe_injective' := forking_map.ext }

variables {oa} {s₀}

/-- Replace the cache from a simulation output with the new forked cache,
without changing the value of the main output. -/
def map_output (f : forking_map oa s₀) :
  α × query_cache spec → α × query_cache spec := λ z, (z.1, f z)

end forking_map

/-- Given a pair of caches `s ≤ s'`, such that some result `z` is possible in both simulations,
the probability of getting that result is higher when starting with the larger cache,
since it has fewer additional choices at which it could diverge from calculating `z`. -/
lemma prob_output_monotone_fork' (oa : oracle_comp spec α) (s₀ : query_cache spec)
  (f : forking_map oa s₀) (z' : α × query_cache spec) :
  ⁅= z' | f.map_output <$> simulate cachingₛₒ oa s₀⁆ ≤
    ⁅= z' | f.map_output <$> simulate cachingₛₒ oa z'.2⁆ :=
begin
  rw [prob_output_map_eq_tsum, prob_output_map_eq_tsum],
  refine ennreal.tsum_le_tsum (λ z, _),
  split_ifs with hz,
  { obtain ⟨rfl⟩ := hz,
    by_cases hzs : z ∈ (simulate cachingₛₒ oa s₀).support,
    { apply prob_output_monotone,
      { exact f.le_to_fun z hzs },
      { exact mem_support_of_le_mem_support oa (f.le_to_fun z hzs)
          z (f.to_fun_le z hzs) hzs } },
    { simp only [hzs, eval_dist_apply_eq_prob_output, prob_output_eq_zero,
        not_false_iff, zero_le'] } },
  { exact le_rfl }
end

/-- Given a pair of caches `s ≤ s'`, such that some result `z` is possible in both simulations,
the probability of getting that result is higher when starting with the larger cache,
since it has fewer additional choices at which it could diverge from calculating `z`. -/
lemma prob_output_monotone'_extra (oa : oracle_comp spec α) (s₀ : query_cache spec)
  (f : forking_map oa s₀) (z' : α × query_cache spec) :
  ⁅= z' | f.map_output <$> simulate cachingₛₒ oa s₀⁆ ≤
    ⁅= z' | f.map_output <$> simulate cachingₛₒ oa z'.2⁆ / (extra_cache_choices s₀ z'.2) :=
begin
  rw [prob_output_map_eq_tsum, prob_output_map_eq_tsum],
  simp_rw [div_eq_mul_inv, ← ennreal.tsum_mul_right],
  refine ennreal.tsum_le_tsum (λ z, _),
  split_ifs with hz,
  { obtain ⟨rfl⟩ := hz,
    by_cases hzs : z ∈ (simulate cachingₛₒ oa s₀).support,
    { exact le_of_eq (prob_output_monotone_extra oa (f.le_to_fun z hzs) z (f.to_fun_le z hzs) hzs) },
    { simp only [hzs, eval_dist_apply_eq_prob_output, prob_output_eq_zero,
        not_false_iff, zero_le'] } },
  { simp only [zero_mul, le_zero_iff]}
end


lemma prob_output_eq_le_prob_output_eq_rewind_base (oa : oracle_comp spec α) (s₀ : query_cache spec)
  (f : forking_map oa s₀) (x : α) :
  ⁅= x | simulate' cachingₛₒ oa s₀⁆ ^ 2 ≤
    ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s₀,
      z' ← simulate cachingₛₒ oa (f z), return (z.1, z'.1)}⁆ :=
calc ⁅= x | simulate' cachingₛₒ oa s₀⁆ ^ 2 =
  (∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
    ⁅= (x, sf) | f.map_output <$> simulate cachingₛₒ oa s₀⁆) ^ 2 :
  begin
    sorry
  end

... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
  ⁅= (x, sf) | f.map_output <$> simulate cachingₛₒ oa s₀⁆ ^ 2 *
    (f <$> simulate cachingₛₒ oa s₀).fin_support.card :
  begin
    sorry,
  end

-- THIS IS THE LEAST CONFIDENT PORTION OF PROOF
... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
  ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
    z' ← simulate cachingₛₒ oa sf, return (f.map_output z, f.map_output z')}⁆ :
  begin
    sorry,
  end

... = ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
  ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
    z' ← simulate cachingₛₒ oa (f z), return (f.map_output z, f.map_output z')}⁆ :
  begin
    sorry,
  end

... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
  ⁅= ((x, sf), x) | do {z ← simulate cachingₛₒ oa s₀,
    z' ← simulate cachingₛₒ oa (f z), return (f.map_output z, z'.1)}⁆ :
  begin
    sorry,
  end

... ≤ ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s₀,
  z' ← simulate cachingₛₒ oa (f z), return (z.1, z'.1)}⁆ : sorry















-------------------------------------- Quarantined

lemma prob_output_eq_le_prob_output_eq_rewind (oa : oracle_comp spec α) (s₀ : query_cache spec)
  (f : forking_map oa s₀) (x : α) :
  let loss_factor : ℝ≥0∞ := ↑(f <$> simulate cachingₛₒ oa s₀).fin_support.card in
  ⁅= x | simulate' cachingₛₒ oa s₀⁆ ^ 2 / loss_factor ≤
    ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s₀,
      z' ← simulate cachingₛₒ oa (f z), return (z.1, z'.1)}⁆ :=

let loss_factor : ℝ≥0∞ := ↑(f <$> simulate cachingₛₒ oa s₀).fin_support.card in
-- First switch to a sum over the possible intermediate values `sf` that will be chosen by `f`.
calc ⁅= x | simulate' cachingₛₒ oa s₀⁆ ^ 2 / loss_factor =
    (∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
      ⁅= (x, sf) | f.map_output <$> simulate cachingₛₒ oa s₀⁆) ^ 2 / loss_factor :
  begin
    sorry
  end
-- Use the loss factor to bring the square inside the summation.
... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= (x, sf) | f.map_output <$> simulate cachingₛₒ oa s₀⁆ ^ 2 :
  begin
    have := ennreal.pow_sum_div_card_le_sum_pow (f <$> simulate cachingₛₒ oa s₀).fin_support
      (λ sf, ⁅= (x, sf) | simulate cachingₛₒ oa s₀ >>= λ z, return (z.1, f z)⁆) (λ _ _, prob_output_ne_top _ _) 1,
    simpa only [pow_one, one_add_one_eq_two] using this
  end

-- Substitute probability for running the computation twice in sequence.
... = ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= ((x, sf), (x, sf)) | f.map_output <$> (simulate cachingₛₒ oa s₀)
          ×ₘ f.map_output <$> (simulate cachingₛₒ oa s₀)⁆ :
  begin
    refine finset.sum_congr rfl (λ sf hsf, _),
    rw [prob_output_product, pow_two],
  end
-- Substitute probability for running the computation twice in sequence.
... = ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
          z' ← simulate cachingₛₒ oa s₀, return (f.map_output z, f.map_output z')}⁆ :
  begin
    refine finset.sum_congr rfl (λ sf hsf, _),
    sorry,
  end
-- Run second computation from the intermediate cache `sf` instead of the base cache `s₀`.
... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
  ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa sf,
    z' ← simulate cachingₛₒ oa sf, return (f.map_output z, f.map_output z')}⁆ :
  begin
    sorry,
  end

... = ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
  ⁅= (x, sf) | f.map_output <$> simulate cachingₛₒ oa sf⁆ ^ 2 : sorry



-- -- Substitute the value `sf` for `f z`, which is equal assuming the probability is non-zero.
-- ... = ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
--         ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
--           z' ← simulate cachingₛₒ oa (f z), return ((z.1, f z), (z'.1, f z'))}⁆ :
--   begin
--     sorry
--   end

-- Improve total probability by just not checking what the second cache returned is.
... ≤ ∑ sf in (f <$> simulate cachingₛₒ oa s₀).fin_support,
        ⁅= ((x, sf), x) | do {z ← simulate cachingₛₒ oa sf,
          z' ← simulate cachingₛₒ oa (f z), return (f.map_output z, z'.1)}⁆ :
  begin
    sorry
  end

-- Revert the summation over the intermediate cache values.
... = ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s₀,
        z' ← simulate cachingₛₒ oa (f z), return (z.1, z'.1)}⁆ :
  begin
    sorry
  end




lemma prob_output_eq_le_prob_output_eq_rewind'
  (oa : oracle_comp spec α) (s₀ : query_cache spec)
  (f : forking_map oa s₀) (x : α) :

  let poss_cuts : finset (query_cache spec) :=
    ((λ z, snd z \ f z) <$> (simulate cachingₛₒ oa s₀)).fin_support in

  ⁅= x | simulate' cachingₛₒ oa s₀⁆ ^ 2 / poss_cuts.card ≤
    ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s₀,
      z' ← simulate cachingₛₒ oa (f z), return (z.1, z'.1)}⁆ :=

let poss_cuts : finset (query_cache spec) :=
  ((λ z, snd z \ f z) <$> (simulate cachingₛₒ oa s₀)).fin_support in
-- First switch to a sum over the possible intermediate values `sf` that will be chosen by `f`.
calc ⁅= x | simulate' cachingₛₒ oa s₀⁆ ^ 2 / poss_cuts.card =
    (∑ sf in poss_cuts,
      ⁅= (x, sf) | do {z ← simulate cachingₛₒ oa s₀, return (z.1, z.2 \ f z)}⁆) ^ 2 / poss_cuts.card :
  begin
    sorry -- "easy"
  end

-- Use the loss factor to bring the square inside the summation.
... ≤ ∑ sf in poss_cuts,
        ⁅= (x, sf) | do {z ← simulate cachingₛₒ oa s₀, return (z.1, z.2 \ f z)}⁆ ^ 2 :
  begin
    have := ennreal.pow_sum_div_card_le_sum_pow poss_cuts
      (λ sf, ⁅= (x, sf) | simulate cachingₛₒ oa s₀ >>= λ z, return (z.1, z.2 \ f z)⁆) (λ _ _, prob_output_ne_top _ _) 1,
    simpa only [pow_one, one_add_one_eq_two] using this
  end

-- Substitute probability for running the computation twice in sequence.
... = ∑ sf in poss_cuts,
        ⁅= ((x, sf), (x, sf)) | (λ (z : α × query_cache spec), (z.1, z.2 \ f z)) <$> (simulate cachingₛₒ oa s₀)
          ×ₘ (λ (z : α × query_cache spec), (z.1, z.2 \ f z)) <$> (simulate cachingₛₒ oa s₀)⁆ :
  begin
    refine finset.sum_congr rfl (λ sf hsf, _),
    rw [prob_output_product, pow_two],
    refl,
  end
-- -- Run second computation from the intermediate cache `sf` instead of the base cache `s₀`.
-- ... ≤ ∑ sf in poss_cuts,
--         ⁅= ((x, sf), (x, sf)) | (λ (z : α × query_cache spec), (z.1, z.2 \ f z)) <$> (simulate cachingₛₒ oa s₀)
--           ×ₘ (λ (z : α × query_cache spec), (z.1, z.2 \ f z)) <$> (simulate cachingₛₒ oa (z.2 \ sf))⁆ :
--   begin
--     refine finset.sum_le_sum (λ sf hsf, _),
--     sorry, -- maybe with s₀ → ∅
--   end
-- Run second computation from the intermediate cache `sf` instead of the base cache `s₀`.
-- ... ≤ ∑ sf in poss_cuts,
--         ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
--           z' ← simulate cachingₛₒ oa (z.2 \ sf), return ((z.1, z.2 \ f z), (z'.1, z'.2 \ f z'))}⁆ :
--   begin
--     sorry -- folding
--   end

-- Substitute the value `sf` for `f z`, which is equal assuming the probability is non-zero.
... = ∑ sf in poss_cuts,
        ⁅= ((x, sf), (x, sf)) | do {z ← simulate cachingₛₒ oa s₀,
          z' ← simulate cachingₛₒ oa (f z), return ((z.1, z.2 \ f z), (z'.1, z'.2 \ f z'))}⁆ :
  begin
    sorry
  end
-- Improve total probability by just not checking what the second cache returned is.
... ≤ ∑ sf in poss_cuts,
        ⁅= ((x, sf), x) | do {z ← simulate cachingₛₒ oa s₀,
          z' ← simulate cachingₛₒ oa (f z), return ((z.1, z.2 \ f z), z'.1)}⁆ :
  begin
    sorry
  end
-- Revert the summation over the intermediate cache values.
... = ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s₀,
        z' ← simulate cachingₛₒ oa (f z), return (z.1, z'.1)}⁆ :
  begin
    sorry
  end



-- lemma output_eq_of_state_eq (oa : oracle_comp spec α)
--   (s s' : query_cache spec) (hs : s ≤ s')
--   (x x' : α) (cache : query_cache spec)
--   (h : (x, cache) ∈ (simulate cachingₛₒ oa s).support)
--   (h' : (x', cache) ∈ (simulate cachingₛₒ oa s).support) :
--   x = x' :=
-- begin
--   induction oa using oracle_comp.induction_on
--     with α a α β oa ob hoa hob i t generalizing s cache,
--   {
--     simp at h h',
--     simp [h.1, h'.1]
--   },
--   {
--     rw [mem_support_simulate_bind_iff] at h h',
--     obtain ⟨a, s, hs, hxa⟩ := h,
--     obtain ⟨a', s', hs', hxa'⟩ := h',
--     specialize hoa a a',
--     specialize hob a x x',
--   }
-- end

end cachingₛₒ
