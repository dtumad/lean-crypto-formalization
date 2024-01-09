/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.query_tracking.query_count.order
import computational_monads.simulation_semantics.constructions.counting_oracle

/-!
# Bounding the Number of Queries by a Computation

This file defines a predicate `is_query_bound oa qb` to represent the fact that
the computation `oa` makes at most as many queries as in the given `query_count`.

See `sec_adv` for computations bundled with a bound on their query count.
-/

open oracle_spec prod (fst) (snd)
open oracle_spec.query_count
open_locale big_operators

variables {spec spec' : oracle_spec} {α β γ : Type}

namespace oracle_comp

/-- `is_query_bound oa qb` means that for each index `i : spec.ι`,
`oa` makes at most `qb.get_count i` calls to the corresponding oracle. -/
def is_query_bound (oa : oracle_comp spec α) (qb : spec.query_count) : Prop :=
∀ z ∈ (simulate countingₛₒ oa ∅).support, snd z ≤ qb

variables (qb qb' : spec.query_count)

lemma is_query_bound_iff_forall (oa : oracle_comp spec α) : is_query_bound oa qb ↔
  ∀ z ∈ (simulate countingₛₒ oa ∅).support, snd z ≤ qb := iff.rfl

lemma is_query_bound_trans {qb qb'} {oa : oracle_comp spec α} (h : is_query_bound oa qb)
  (h' : qb ≤ qb') : is_query_bound oa qb' := λ z hz, le_trans (h z hz) h'

@[simp] lemma is_query_bound_return (a : α) :
  is_query_bound (return a : oracle_comp spec α) qb :=
λ z hz, le_of_eq_of_le ((mem_support_simulate_return_iff _ _ _ z).1 hz).2 qb.empty_le

lemma is_query_bound_return_iff_true (a : α) :
  is_query_bound (return a : oracle_comp spec α) qb ↔ true :=
⟨λ h, true.intro, λ h, is_query_bound_return qb a⟩

@[simp] lemma is_query_bound_query_iff (i : spec.ι) (t : spec.domain i) :
  is_query_bound (query i t) qb ↔ i ∈ qb.active_oracles :=
begin
  rw [is_query_bound_iff_forall],
  refine ⟨λ h, _, λ h z hz, _⟩,
  { specialize h (default, of_nat i 1) (by simp),
    simpa only [of_nat_le_iff, indexed_list.one_le_get_count_iff] using h },
  { rw [simulate_query, counting_oracle.apply_eq, increment_empty_eq_of_nat,
      support_map, support_query, set.image_univ, set.mem_range] at hz,
    obtain ⟨x, hx⟩ := hz,
    simpa [← hx] using h }
end

lemma of_nat_is_query_bound_query (i : spec.ι) (t : spec.domain i) :
  is_query_bound (query i t) (of_nat i 1) :=
by simp only [is_query_bound_query_iff, active_oracles_of_nat, nat.one_ne_zero,
  if_false, finset.mem_singleton]

lemma is_query_bound_bind_iff (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  is_query_bound (oa >>= ob) qb ↔ ∀ z ∈ (simulate countingₛₒ oa ∅).support,
    ∀ z' ∈ (simulate countingₛₒ (ob (fst z)) ∅).support, snd z + snd z' ≤ qb :=
begin
  rw [is_query_bound_iff_forall],
  refine ⟨λ h z hz z' hz', _, λ h z' hz', _⟩,
  { refine h (z'.1, z.2 + z'.2) _,
    rw [mem_support_simulate_bind_iff'],
    refine ⟨z, hz, _⟩,
    rw [counting_oracle.simulate_eq_map_add_left_simulate_empty, mem_support_map_iff],
    exact ⟨z', hz', rfl⟩ },
  { rw [simulate_bind, mem_support_bind_iff] at hz',
    obtain ⟨z, hz, hz'⟩ := hz',
    rw [counting_oracle.simulate_eq_map_add_left_simulate_empty, mem_support_map_iff] at hz',
    obtain ⟨z'', hz'', h'⟩ := hz',
    exact h' ▸ h z hz z'' hz'' }
end

lemma is_query_bound_bind_iff' (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  is_query_bound (oa >>= ob) qb ↔ ∀ z ∈ (simulate countingₛₒ oa ∅).support,
    snd z ≤ qb ∧ is_query_bound (ob (fst z)) (qb - snd z) :=
begin
  simp_rw [is_query_bound_bind_iff, is_query_bound_iff_forall],
  refine ⟨λ h z hz, ⟨_, _⟩, λ h z hz z' hz', _⟩,
  { obtain ⟨z', hz'⟩ := support_nonempty (simulate countingₛₒ (ob z.fst) ∅),
    exact le_trans le_self_add (h z hz z' hz') },
  { exact λ z' hz', le_tsub_of_add_le_left (h z hz z' hz') },
  { exact add_le_of_le_tsub_left_of_le (h z hz).1 ((h z hz).2 z' hz') }
end

lemma add_is_query_bound_bind {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  {qb qb' : spec.query_count} (h : is_query_bound oa qb) (h' : ∀ x, is_query_bound (ob x) qb') :
  is_query_bound (oa >>= ob) (qb + qb') :=
begin
  rw [is_query_bound_bind_iff'],
  refine λ z hz, ⟨le_add_of_le_left (h z hz), λ z' hz', _⟩,
  rw [add_comm, add_tsub_assoc_of_le (h z hz)],
  refine le_trans (h' z.1 z' hz') le_self_add,
end

@[simp] lemma is_query_bound_query_bind_iff (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α) : is_query_bound (query i t >>= oa) qb ↔
    i ∈ qb.active_oracles ∧ ∀ u, is_query_bound (oa u) (qb.decrement i 1) :=
begin
  simp_rw [is_query_bound_bind_iff', decrement_eq_sub_of_nat,
    simulate_query, counting_oracle.mem_support_apply_iff],
  refine ⟨λ h, ⟨_, λ u, _⟩, λ h z hz, _⟩,
  { have := (h ⟨default, of_nat i 1⟩ (by simp)).1,
    simpa only [of_nat_le_iff, indexed_list.one_le_get_count_iff] using this },
  { exact (h (u, of_nat i 1) (by simp)).2 },
  { rw [← hz, increment_empty_eq_of_nat, of_nat_le_iff, indexed_list.one_le_get_count_iff],
    exact ⟨h.1, h.2 z.1⟩ }
end

lemma is_query_bound_of_bind_left {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
  {qb : spec.query_count} (h : is_query_bound (oa >>= ob) qb) : is_query_bound oa qb :=
(λ z hz, ((is_query_bound_bind_iff' _ _ _).1 h z hz).1)

-- lemma is_query_bound_of_bind_right {oa : oracle_comp spec α} {ob : α → oracle_comp spec β}
--   {qb : spec.query_count} (h : is_query_bound (oa >>= ob) qb) (x : α)
--   (hx : x ∈ oa.support) : is_query_bound (ob x) qb :=
-- begin
--   rw [is_query_bound_bind_iff'] at h,
--   intros z' hz',
-- end

@[simp] lemma empty_is_query_bound_iff (oa : oracle_comp spec α) :
  is_query_bound oa ∅ ↔ ∃ a, oa = return a :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa,
  { simp only [is_query_bound_return_iff_true, oracle_comp.return_eq_return_iff, exists_eq'] },
  { simp [is_query_bound_bind_iff'] }
end

@[simp] lemma is_query_bound_map_iff (oa : oracle_comp spec α) (f : α → β) :
  is_query_bound (f <$> oa) qb ↔ is_query_bound oa qb :=
by simp_rw [oracle_comp.map_eq_bind_return_comp, is_query_bound_bind_iff', is_query_bound_return,
  and_true, is_query_bound_iff_forall]

section query_bound

/-- `query_bound oa` is the minimal `qc : query_count` with `is_query_bound oa qc` -/
noncomputable def query_bound : Π {α : Type}, oracle_comp spec α → spec.query_count
| _ (pure' _ a) := ∅
| _ (query_bind' i t _ oa) := of_nat i 1 + finset.univ.sup (λ u, query_bound (oa u))

@[simp] lemma query_bound_return (a : α) : query_bound (return a : oracle_comp spec α) = ∅ := rfl

@[simp] lemma query_bound_query (i : spec.ι) (t : spec.domain i) :
  query_bound (query i t) = of_nat i 1 :=
begin
  rw [query_def, query_bound, indexed_list.add_right_eq_self_iff],
  refine finset.sup_const finset.univ_nonempty ∅,
end

lemma query_bound_query_bind (i : spec.ι) (t : spec.domain i)
  (oa : spec.range i → oracle_comp spec α) : query_bound (query i t >>= oa) =
    of_nat i 1 + finset.univ.sup (λ u, query_bound (oa u)) :=
by rw [← query_bind'_eq_query_bind, query_bound]

lemma query_bound_is_query_bound (oa : oracle_comp spec α) : is_query_bound oa (query_bound oa) :=
begin
  induction oa with α a i t α oa hoa,
  { exact is_query_bound_return _ _ },
  { rw [query_bound, query_bind'_eq_query_bind],
    exact add_is_query_bound_bind (of_nat_is_query_bound_query i t)
      (λ u z hz, finset.le_sup_of_le (finset.mem_univ u) (hoa u z hz)) }
end

lemma query_bound_le_iff (oa : oracle_comp spec α) : query_bound oa ≤ qb ↔ is_query_bound oa qb :=
begin
  refine ⟨λ h, is_query_bound_trans (query_bound_is_query_bound oa) h, _⟩,
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing qb,
  { exact λ _, indexed_list.empty_le _ },
  { rw [is_query_bound_query_bind_iff, query_bound_query_bind],
    refine λ h, add_le_of_le_tsub_left_of_le _ (finset.sup_le (λ u hu, hoa u _ (h.2 u))),
    simp [h.1] }
end

lemma query_bound_le {oa : oracle_comp spec α} {qb} (h : is_query_bound oa qb) :
  query_bound oa ≤ qb := (query_bound_le_iff qb oa).2 h

lemma is_query_bound_of_le {oa : oracle_comp spec α} {qb} (h : query_bound oa ≤ qb) :
  is_query_bound oa qb := (query_bound_le_iff qb oa).1 h

end query_bound

section simulate

variables {S S' : Type}

/-- If we have bounds `qbs` on the number of queries made by a simulation oracle,
then we can bound the number of queries after simulation by multiplying this bound
by the number of times it appears in the bound of the original computation. -/
lemma nsmul_is_query_bound_simulate (so : sim_oracle spec spec' S) {oa : oracle_comp spec α}
  {qb : spec.query_count} (h : is_query_bound oa qb) (qbs : spec.ι → spec'.query_count)
  (hqbs : ∀ i t s, is_query_bound (so i (t, s)) (qbs i)) (s : S) :
  is_query_bound (simulate so oa s) (∑ i in qb.active_oracles, qb.get_count i • qbs i) :=
begin
  induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing qb s,
  { exact is_query_bound_return _ (a, s) },
  { rw [simulate_bind, is_query_bound_bind_iff],
    intros z hz z' hz',
    rw [simulate_query] at hz,
    obtain ⟨hi, hd⟩ := (is_query_bound_query_bind_iff _ _ _ _).1 h,
    refine le_of_le_of_eq (add_le_add (hqbs i t s z hz) (hoa z.1.1 z.1.2 (hd z.1.1) z' hz')) _,
    rw [← (finset.add_sum_erase _ _ hi), active_oracles_decrement],
    split_ifs with hi',
    { rw [le_antisymm hi' (qb.one_le_get_count hi), one_smul, add_left_cancel_iff],
      refine finset.sum_congr rfl (λ j hj, _),
      rw [finset.mem_erase] at hj,
      simp only [get_count_decrement, ne.symm hj.1, if_false, tsub_zero] },
    { simp only [← finset.add_sum_erase _ _ hi, ← add_assoc, ← succ_nsmul, add_left_cancel_iff,
        ← get_count_increment_self, increment_decrement_eq_self _ _ _ (le_of_not_le hi') ],
      refine finset.sum_congr rfl (λ j hj, _),
      rw [finset.mem_erase] at hj,
      simp only [get_count_decrement, ne.symm hj.1, if_false, tsub_zero] } }
end

@[simp] lemma is_query_bound_simulate'_iff (so : sim_oracle spec spec' S)
  (oa : oracle_comp spec α) (s : S) (qb : spec'.query_count) :
  is_query_bound (simulate' so oa s) qb ↔ is_query_bound (simulate so oa s) qb :=
is_query_bound_map_iff qb _ fst

lemma nsmul_is_query_bound_simulate' (so : sim_oracle spec spec' S) {oa : oracle_comp spec α}
  {qb : spec.query_count} (h : is_query_bound oa qb) (qbs : spec.ι → spec'.query_count)
  (hqbs : ∀ i t s, is_query_bound (so i (t, s)) (qbs i)) (s : S) :
  is_query_bound (simulate' so oa s) (∑ i in qb.active_oracles, qb.get_count i • qbs i) :=
(is_query_bound_simulate'_iff so oa s _).2 (nsmul_is_query_bound_simulate so h qbs hqbs s)


end simulate


-- @[simp] lemma is_query_bound_seq_iff (oa : oracle_comp spec α) (og : oracle_comp spec (α → β)) :
--   is_query_bound (og <*> oa) qb ↔ ∃ qb₁ qb₂, qb₁ + qb₂ ≤ qb ∧
--     is_query_bound oa qb₁ ∧ is_query_bound og qb₂ :=
-- begin
--   simp_rw [seq_eq_bind_map, is_query_bound_bind_iff', is_query_bound_map_iff],
--   refine ⟨λ h, _, λ h, _⟩,
--   {
--     by_contra h',
--     -- simp at h h',
--     simp at h',
--     obtain ⟨z, hz⟩ := support_nonempty ((simulate countingₛₒ og ∅)),
--     obtain ⟨z', hz'⟩ := support_nonempty (simulate countingₛₒ oa ∅),
--     specialize h z hz,
--     specialize h' z.2 z'.2,
--     obtain ⟨h1, h2⟩ := h,
--     specialize h2 z' hz',
--     specialize h' (add_le_of_le_tsub_left_of_le h1 h2),
--   }
-- end

end oracle_comp

section sim_oracle

open oracle_comp

variables {S S' : Type}

lemma is_tracking.is_query_bound_simulate_iff (so : sim_oracle spec spec S) [so.is_tracking]
  (h' : ∀ i t s, (simulate countingₛₒ (so i (t, s)) ∅).support = 
    (λ z, (z, of_nat i 1)) '' (so i (t, s)).support)
  (hso' : ∀ i t s qb, is_query_bound (so i (t, s)) qb → i ∈ qb.active_oracles)
  (oa : oracle_comp spec α) (s : S) (qb : spec.query_count) :
  is_query_bound (simulate so oa s) qb ↔ is_query_bound oa qb :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { induction oa using oracle_comp.induction_on' with α a i t α oa hoa generalizing qb s,
    { exact is_query_bound_return qb a },
    { rw [simulate_bind, simulate_query] at h,
      rw [is_query_bound_query_bind_iff],
      refine ⟨hso' i t s qb (is_query_bound_of_bind_left h), λ u z hz, _⟩,      
      rw [is_query_bound_bind_iff'] at h,
      obtain ⟨s', hs'⟩ := sim_oracle.is_tracking.exists_mem_support_apply so i t s u,
      refine hoa u (qb - of_nat i 1) _ (h ⟨⟨u, s'⟩, of_nat i 1⟩ _).2 z hz,
      simpa only [h', support_map] using apply_mem_support_map _ (λ z, (z, of_nat i 1)) _ hs' } },
  { have hso : ∀ i t s, is_query_bound (so i (t, s)) (of_nat i 1),
    { refine λ i t s z hz, _,
      rw [h'] at hz,
      refine let ⟨_, _, hz⟩ := hz in hz ▸ le_rfl },
    refine is_query_bound_trans (nsmul_is_query_bound_simulate so h (λ i, of_nat i 1) hso s)
      (le_of_eq (trans _ (symm qb.eq_sum_active_oracles_of_nat_get_count))),
    simp only [nsmul_of_nat, mul_one] }
end

lemma counting_oracle.is_query_bound_simulate_iff (oa : oracle_comp spec α) (s : spec.query_count)
  (qb : spec.query_count) : is_query_bound (simulate countingₛₒ oa s) qb ↔ is_query_bound oa qb := 
begin
  refine is_tracking.is_query_bound_simulate_iff countingₛₒ _ _ oa s qb,
  { refine λ i t s, set.ext (λ z, by simp) },
  { refine λ i t s qb h, by simpa using h }
end

end sim_oracle