/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_cache.get_or_else
import computational_monads.query_tracking.query_cache.add_fresh_queries
import computational_monads.query_tracking.query_cache.sdiff
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

lemma apply_eq_of_mem (h : z.1 ∈ᵢ z.2) :
  cachingₛₒ i z = return ((z.2.lookup i z.1).get_or_else default, z.2) := by simp [h]

lemma apply_eq_of_mem' (h : t ∈ᵢ s₀) :
  cachingₛₒ i (t, s₀) = return ((s₀.lookup i t).get_or_else default, s₀) := apply_eq_of_mem h

lemma apply_eq_of_not_mem (h : z.1 ∉ᵢ z.2) :
  cachingₛₒ i z = query i z.1 >>= λ u, return (u, [i, z.1 ↦ u; z.2]) := by simp [h]

lemma apply_eq_of_not_mem' (h : t ∉ᵢ s₀) :
  cachingₛₒ i (t, s₀) = query i t >>= λ u, return (u, [i, t ↦ u; s₀]) := apply_eq_of_not_mem h

lemma apply_eq_of_lookup_eq_some {u} (h : s₀.lookup i t = some u) :
  cachingₛₒ i (t, s₀) = return (u, s₀) := get_or_else_of_lookup_eq_some _ _ h

end apply

variables (oa : oracle_comp spec α) (s₀ s : query_cache spec)

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
  z ≠ z' ↔ ∃ i t, t ∈ᵢ z.2 ∧ t ∈ᵢ z'.2 ∧ z.2.lookup i t ≠ z'.2.lookup i t :=
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
        refine ⟨i, t, mem_of_le_of_mem hz htx,
          mem_of_le_of_mem hz' htx', _⟩,
        rwa [lookup_eq_lookup_of_le_of_mem hz htx,
          lookup_eq_lookup_of_le_of_mem hz' htx'] } },
    { by_cases hs₀ : t ∈ᵢ s₀,
      { simp [simulate_query, hs₀] at hz hz',
        refine (h (hz.trans hz'.symm)).elim },
      { simp [simulate_query, hs₀] at hz hz',
        obtain ⟨u, rfl⟩ := hz,
        obtain ⟨u', rfl⟩ := hz',
        refine ⟨i, t, _⟩,
        simp only [mem_cache_query_same_input, true_and,
          lookup_cache_query_same_input, ne.def, option.some_inj],
        simpa only [ne.def, prod.eq_iff_fst_eq_snd_eq, not_and_distrib,
          cache_query_eq_cache_query_iff_of_same_cache, or_self] using h } } },
  { exact let ⟨i, t, hzt, hzt', hz⟩ := h in λ h',
      (query_cache.ne_of_lookup_ne _ _ i t hz) (prod.eq_iff_fst_eq_snd_eq.1 h').2 }
end

/-- Given a possible result `z` of simulating a computation `oa >>= ob` with a caching oracle,
we get a stronger version `mem_support_simulate_bind_iff` that includes uniqueness of the
intermediate result (since all choices made must align with the cached values in `z`).  -/
lemma mem_support_simulate_bind_iff (ob : α → oracle_comp spec β)
  (z : β × query_cache spec) : z ∈ (simulate cachingₛₒ (oa >>= ob) s₀).support ↔
    ∃! (y : α × query_cache spec), y ∈ (simulate cachingₛₒ oa s₀).support ∧
      z ∈ (simulate cachingₛₒ (ob y.1) y.2).support :=
begin
  rw [mem_support_simulate_bind_iff'],
  refine ⟨λ h, exists_unique_of_exists_of_unique h _, λ h, exists_of_exists_unique h⟩,
  rintros y y' ⟨hy, hyz⟩ ⟨hy', hyz'⟩,
  by_contradiction h,
  obtain ⟨i, t, hty, hty', ht⟩ := (ne_iff_exists_lookup_ne_of_mem_support_simulate hy hy').1 h,
  rwa [← lookup_eq_lookup_of_le_of_mem (le_of_mem_support_simulate _ hyz) hty,
    ← lookup_eq_lookup_of_le_of_mem (le_of_mem_support_simulate _ hyz') hty',
    ne.def, eq_self_iff_true, not_true] at ht,
end

lemma exists_unique_mem_support_of_le (oa : oracle_comp spec α) {s₀ s₁ : query_cache spec}
  (hs₀₁ : s₀ ≤ s₁) (z₁ : α × query_cache spec) (hz : z₁ ∈ (simulate cachingₛₒ oa s₁).support) :
  ∃! (z₀ : α × query_cache spec), z₀.2 ≤ z₁.2 ∧ z₀ ∈ (simulate cachingₛₒ oa s₀).support :=
begin
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing s₀ s₁ z₁,
  { rw [support_simulate_return, set.mem_singleton_iff, prod.eq_iff_fst_eq_snd_eq] at hz,
    simp [hz.1, hz.2],
    exact ⟨⟨a, s₀⟩, ⟨hs₀₁, rfl⟩, λ s hs, hs.2⟩ },
  {
    sorry,
  },
  {
    sorry,
  }
end

lemma exists_unique_state_mem_support_of_le (oa : oracle_comp spec α) {s₀ s₁ : query_cache spec}
  (hs₀₁ : s₀ ≤ s₁) (z : α × query_cache spec) (hz : z ∈ (simulate cachingₛₒ oa s₁).support) :
  ∃! (s : query_cache spec), s ≤ z.2 ∧ (z.1, s) ∈ (simulate cachingₛₒ oa s₀).support :=
begin
  induction oa using oracle_comp.induction_on
    with α a α β oa ob hoa hob i t generalizing s₀ s₁ z,
  { rw [support_simulate_return, set.mem_singleton_iff, prod.eq_iff_fst_eq_snd_eq] at hz,
    suffices : ∃! (s : query_cache spec), s ≤ s₁ ∧ s = s₀,
    by simpa [hz.1, hz.2] using this,
    exact ⟨s₀, ⟨hs₀₁, rfl⟩, λ s hs, hs.2⟩ },
  {
    rw [mem_support_simulate_bind_iff'] at hz,
    obtain ⟨y, hy, hyz⟩ := hz,
    specialize hoa y hs₀₁ hy,
    refine exists_unique_of_exists_of_unique _ _,
    {

      obtain ⟨s₁', hs₁'⟩ := exists_of_exists_unique hoa,
      clear hoa,
      specialize hob y.1 z hs₁'.1 hyz,
      obtain ⟨s', hs'⟩ := exists_of_exists_unique hob,
      clear hob,
      refine ⟨s', hs'.1, _⟩,
      rw [oracle_comp.mem_support_simulate_bind_iff],
      refine ⟨y.1, s₁', hs₁'.2, hs'.2⟩,
    },
    {
      intros s s' hs hs',
      rw [mem_support_simulate_bind_iff'] at hs hs',
      obtain ⟨⟨y1, s₂⟩, hs₂⟩ := hs.2,
      obtain ⟨⟨y2, s₂'⟩, hs₂'⟩ := hs'.2,
      have := @unique_of_exists_unique _ _ hoa s₂ s₂',
      simp only [] at this hs₂ hs₂',
      sorry,
    }
  },
  {
    by_cases hs₁ : t ∈ᵢ s₁,

    {
      rw [mem_iff_exists_lookup_eq_some] at hs₁,
      obtain ⟨u, hu⟩ := hs₁,
      refine ⟨[i, t ↦ u; s₀], ⟨_, _⟩, _⟩,
      {
        refine trans _ (le_of_mem_support_simulate z hz),
        sorry,
        -- rwa [cache_query_le_iff_of_le hs],
      },
      {
        rw [simulate_query, apply_eq_of_lookup_eq_some hu, mem_support_return_iff] at hz,
        simp only [hz, support_simulate_query, apply_eq],
        by_cases hs₀ : t ∈ᵢ s₀,

        {
          sorry,
          -- simp [support_get_or_else_of_mem _ _ hs₀, (lookup_eq_lookup_of_le_of_mem hs hs₀).symm.trans hu],
        },
        {
          simp only [support_get_or_else_of_not_mem _ _ hs₀, support_query, set.image_univ,
            set.mem_range, prod.mk.inj_iff, exists_eq_left],
        },
      },
      {
        rintro s ⟨hs, hsz⟩,
        rw [simulate_query, apply_eq_of_lookup_eq_some hu, mem_support_return_iff,
            prod.eq_iff_fst_eq_snd_eq] at hz,
        by_cases hs₀ : t ∈ᵢ s₀,

        {
          simp [simulate_query, hs₀, hz.1] at hsz,
          rw [hsz.2, eq_comm, cache_query_eq_self_iff, hsz.1],
          rw [mem_iff_exists_lookup_eq_some] at hs₀,
          obtain ⟨u', hu'⟩ := hs₀,
          rw [hu', option.get_or_else_some],
        },
        {
          simp [simulate_query, hs₀, hz.1] at hsz,
          exact hsz.symm
        },
      }
    },
    {
      sorry,
      -- have hs₀ : t ∉ᵢ s₀ := not_mem_of_le_of_not_mem hs hs₁,
      -- simp [hs₀, hs₁, support_simulate_query] at hz ⊢,
      -- obtain ⟨x, rfl⟩ := hz,
      -- exact ⟨[i, t ↦ x; s₀], ⟨(cache_query_le_cache_query_iff_of_not_mem x hs₀ hs₁).2 hs, rfl⟩,
      --   λ s hs, by rw [← hs.2]⟩ },
  } }
end

lemma mem_support_of_le_mem_support (oa : oracle_comp spec α) {s₀ s : query_cache spec}
  (hs : s₀ ≤ s) (z : α × query_cache spec) (hzs : s ≤ z.2)
  (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  z ∈ (simulate cachingₛₒ oa s).support :=
begin
  sorry,
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
    by_cases hs₀ : t ∈ᵢ s₀,

    { simp only [apply_eq_of_mem' hs₀, mem_support_return_iff, prod.eq_iff_fst_eq_snd_eq,
        apply_eq_of_mem' (mem_of_le_of_mem hs hs₀), exists_eq_right,
        ← lookup_eq_lookup_of_le_of_mem hs hs₀] at ⊢ hs',
      exact hs'.1 },
    { simp_rw [apply_eq_of_not_mem' hs₀, mem_support_query_bind_return_iff,
        prod.mk.inj_iff, exists_eq_left, exists_eq'] }, },
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
  extra_cache_choices s [i, t ↦ u; s] = if t ∈ᵢ s then 1 else fintype.card (spec.range i) :=
by split_ifs with h; simp [extra_cache_choices, cache_query_sdiff_self, h]

end extra_cache_choices

/-- Probability of getting to a final result given a partial cache for queries is given by
the product of probabilities that each additional query gets the expected result.
Note that this requires `z` be in the support of the simulation (as the empty product is `1`). -/
lemma finite_version {oa : oracle_comp spec α} {s₀ : query_cache spec}
  {z : α × query_cache spec} (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  ⁅= z | simulate cachingₛₒ oa s₀⁆ = (extra_cache_choices s₀ z.2)⁻¹ :=
begin
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
    rw [prob_output_simulate_bind_of_mem_support _ _ _ hy hyz, hoa hy, hob y.1 hyz,
      ← ennreal.mul_inv (or.inr (ennreal.nat_ne_top _)) ((or.inl (ennreal.nat_ne_top _))),
      ← nat.cast_mul, extra_cache_choices_mul_trans],
  },
  {
    simp only [simulate_query, apply_eq] at hz ⊢,
    by_cases hs₀ : t ∈ᵢ s₀,
    {
      simp only [hs₀, get_or_else_of_mem, support_return, set.mem_singleton_iff] at hz,
      simp only [hz, extra_cache_choices_self, nat.cast_one, inv_one,
        get_or_else_of_mem _ _ hs₀],
      refine prob_output_return_self _ _,
    },
    {
      simp only [get_or_else_of_not_mem _ _ hs₀, support_bind_return, support_query,
        set.image_univ, set.mem_range] at hz,
      obtain ⟨u, rfl⟩ := hz,
      simp [hs₀, get_or_else_of_not_mem, extra_cache_choices_cache_query, if_true],
      refine trans (prob_output_bind_return_eq_single _ _ _ u _) (prob_output_query_eq_inv _ _ _),
      refine set.ext (λ u', _),
      simp [cache_query_eq_cache_query_iff_of_same_cache],
    },
  }
end

lemma prob_output_monotone_extra (oa : oracle_comp spec α) {s₀ s : query_cache spec}
  (hs : s₀ ≤ s) (z : α × query_cache spec) (hzs : s ≤ z.2)
  (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  ⁅= z | simulate cachingₛₒ oa s₀⁆ =
    ⁅= z | simulate cachingₛₒ oa s⁆ / ↑(extra_cache_choices s₀ s) :=
begin
  have hz' : z ∈ (simulate cachingₛₒ oa s).support,
  from mem_support_of_le_mem_support oa hs z hzs hz,
  rw [finite_version hz', finite_version hz, div_eq_mul_inv,
    ← ennreal.mul_inv (or.inr (ennreal.nat_ne_top _)) (or.inl (ennreal.nat_ne_top _)), ← nat.cast_mul, mul_comm,
      extra_cache_choices_mul_trans],
end

lemma prob_output_monotone_extra_inv (oa : oracle_comp spec α) {s₀ s : query_cache spec}
  (hs : s₀ ≤ s) (z : α × query_cache spec) (hzs : s ≤ z.2)
  (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  ⁅= z | simulate cachingₛₒ oa s₀⁆ =
    ⁅= z | simulate cachingₛₒ oa s⁆ * (↑(extra_cache_choices s₀ s))⁻¹ :=
begin
  sorry
end

lemma prob_output_monotone_extra' (oa : oracle_comp spec α) {s₀ s : query_cache spec}
  (hs : s₀ ≤ s) (z : α × query_cache spec) (hzs : s ≤ z.2)
  (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
  ⁅= z | simulate cachingₛₒ oa s₀⁆ * ↑(extra_cache_choices s₀ s) =
    ⁅= z | simulate cachingₛₒ oa s⁆ :=
begin
  rw [prob_output_monotone_extra oa hs z hzs hz, div_eq_mul_inv,
    mul_assoc, ennreal.inv_mul_cancel, mul_one],
  simp [extra_cache_choices, finset.prod_eq_zero_iff],
  refine ennreal.nat_ne_top _,
end

-- lemma prob_output_monotone_extra_sim' (oa : oracle_comp spec α) {s₀ s : query_cache spec}
--   (hs : s₀ ≤ s) (x : α)
--   (hz : x ∈ (simulate' cachingₛₒ oa s₀).support) :
--   ⁅= x | simulate' cachingₛₒ oa s⁆ ≤
--     ⁅= x | simulate' cachingₛₒ oa s₀⁆ * (extra_cache_choices s₀ s) :=
-- begin
--   simp only [prob_output_simulate', ← ennreal.tsum_mul_right],
--   refine ennreal.tsum_le_tsum (λ s', _),
--   by_cases hz : (x, s') ∈ (simulate cachingₛₒ oa s₀).support,
--   {
--     sorry,
--   },
--   {
--     rw [prob_output_eq_zero hz, zero_mul, le_zero_iff],
--     sorry,
--   }
-- end



/-- A `forking_map` for a computation `oa` and initial state `s₀` is one that is well behaved
for forking a computation, via mapping output of simulation to a new initial state for running
the computation again. Requires that the mapping stays between the initial and final cache. -/
@[ext] structure forking_map (oa : oracle_comp spec α) (s₀ : query_cache spec) :=
(to_fun : α × query_cache spec → query_cache spec)
(le_to_fun : ∀ z ∈ (simulate cachingₛₒ oa s₀).support, s₀ ≤ to_fun z)
(to_fun_le : ∀ z ∈ (simulate cachingₛₒ oa s₀).support, to_fun z ≤ z.2)
(sdiff_to_fun_const {z z' : α × query_cache spec} (hz : z.1 = z'.1) :
  (z.2 \ to_fun z).cached_inputs = (z'.2 \ to_fun z').cached_inputs)

namespace forking_map

variables {oa} {s₀} (f : forking_map oa s₀)

lemma sdiff_to_fun_const' (x : α) (s s' : query_cache spec) :
  (s \ f.to_fun (x, s)).cached_inputs = (s \ f.to_fun (x, s)).cached_inputs :=
f.sdiff_to_fun_const rfl

section fun_like

instance fun_like (oa : oracle_comp spec α) (s₀ : query_cache spec) :
  fun_like (forking_map oa s₀) (α × query_cache spec) (λ z, query_cache spec) :=
{ coe := forking_map.to_fun,
  coe_injective' := forking_map.ext }

lemma coe_to_fun_apply (z : α × query_cache spec) : f z = f.to_fun z := rfl

end fun_like

section map_output

/-- Replace the cache from a simulation output with the new forked cache,
without changing the value of the main output. -/
def map_output (z : α × query_cache spec) : α × query_cache spec := (z.1, f z)

lemma sdiff_map_output_const (z z' : α × query_cache spec) (hz : z.1 = z'.1) :
  (z.2 \ (f.map_output z).2).cached_inputs = (z'.2 \ (f.map_output z').2).cached_inputs :=
f.sdiff_to_fun_const hz

lemma sdiff_map_output : sorry := sorry

end map_output

end forking_map

-- /-- Given a pair of caches `s ≤ s'`, such that some result `z` is possible in both simulations,
-- the probability of getting that result is higher when starting with the larger cache,
-- since it has fewer additional choices at which it could diverge from calculating `z`. -/
-- lemma prob_output_monotone'_extra' (oa : oracle_comp spec α) (s₀ s : query_cache spec) (hs : s₀ ≤ s)
--   (f : forking_map oa s₀) (z : α × query_cache spec) (hzs : s ≤ z.2)
--   (hz : z ∈ (simulate cachingₛₒ oa s₀).support) :
--   ⁅= z | f.map_output <$> simulate cachingₛₒ oa s₀⁆ =
--     ⁅= z | f.map_output <$> simulate cachingₛₒ oa s⁆ / (extra_cache_choices s₀ s) :=
-- begin
--   rw [prob_output_map_eq_tsum, prob_output_map_eq_tsum],
--   simp_rw [div_eq_mul_inv, ← ennreal.tsum_mul_right],
--   refine tsum_congr (λ z, _),
--   split_ifs with hz,
--   { obtain ⟨rfl⟩ := hz,
--     apply prob_output_monotone_extra_inv,
--     rw [extra_cache_choices],
--     by_cases hzs : z ∈ (simulate cachingₛₒ oa s₀).support,
--     { exact le_of_eq (prob_output_monotone_extra oa (f.le_to_fun z hzs) z (f.to_fun_le z hzs) hzs) },
--     { simp only [hzs, eval_dist_apply_eq_prob_output, prob_output_eq_zero,
--         not_false_iff, zero_le'] } },
--   { simp only [zero_mul, le_zero_iff]}
-- end

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

lemma prob_output_main' (oa : oracle_comp spec α) (s : query_cache spec)
  (f : forking_map oa s) (x : α) :
  ⁅= (x, x) | do {x₁ ← simulate' cachingₛₒ oa s,
      x₂ ← simulate' cachingₛₒ oa s, return (x₁, x₂)}⁆ ≤
    ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s,
      x₂ ← simulate' cachingₛₒ oa (f z), return (z.1, x₂)}⁆ :=
let fork_points : finset (query_cache spec) :=
  finset.image f {z ∈ (simulate cachingₛₒ oa s).fin_support | z.1 = x} in
let k : ℝ≥0∞ := sorry in
calc ⁅= (x, x) | simulate' cachingₛₒ oa s ×ₘ simulate' cachingₛₒ oa s⁆ =
  ⁅= x | simulate' cachingₛₒ oa s⁆ ^ 2 :
    begin
      sorry
    end
  ... = (∑ sf in fork_points, ⁅= x | simulate' cachingₛₒ oa s⁆ * fork_points.card⁻¹) ^ 2 :
    begin
      sorry
    end

  ... ≤ (∑ sf in fork_points, ⁅= x | simulate' cachingₛₒ oa sf⁆ * (extra_cache_choices s sf)⁻¹) ^ 2 :
    begin
      sorry
    end


  ... ≤ ∑ sf in fork_points, ⁅= x | simulate' cachingₛₒ oa sf⁆ *
            ⁅= x | simulate' cachingₛₒ oa sf⁆ * (extra_cache_choices s sf)⁻¹ :
    begin
      sorry
    end


  ... = ∑ sf in fork_points, ⁅= (x, sf) | f.map_output <$> simulate cachingₛₒ oa s⁆ *
          ⁅= x | simulate' cachingₛₒ oa sf⁆ :
    begin
      sorry,
    end
  ... = ∑ sf in fork_points, ⁅= ((x, sf), x) | do {z ← f.map_output <$> simulate cachingₛₒ oa s,
          x₂ ← simulate' cachingₛₒ oa sf, return (z, x₂)}⁆ :
    begin
      sorry,
    end
  ... ≤ ⁅= (x, x) | do {z ← simulate cachingₛₒ oa s,
      x₂ ← simulate' cachingₛₒ oa (f z), return (z.1, x₂)}⁆ :
    begin
      sorry
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


end cachingₛₒ
