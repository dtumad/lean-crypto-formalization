import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.constructions.tracking_oracle

open oracle_comp oracle_spec

variables {A B : Type} {spec spec' spec'' : oracle_spec}
  (oa : oracle_comp spec A)

/-- Simulate a computation without making use of the internal state.
  We use the `unit` type as the state in this case, so all possible states are equal.
  Implemented as a `tracking_oracle` where the state isn't actually tracking anything -/
def stateless_oracle (spec spec' : oracle_spec)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)) :
  simulation_oracle spec spec' :=
⟪o | λ _ _ _ _, (), ()⟫

notation `⟪` o `⟫` := stateless_oracle _ _ o

variables (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i))
  (o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i))

@[simp]
lemma S_stateless_oracle :
  ⟪o⟫.S = unit := rfl

@[simp]
lemma default_state_stateless_oracle :
  ⟪o⟫.default_state = () := rfl

@[simp]
lemma stateless_oracle_apply (i : spec.ι) (t : spec.domain i) (s : unit) :
  ⟪o⟫.o i (t, s) = o i t >>= λ u, return (u, ()) := rfl

section simulate

@[simp]
lemma support_simulate_stateless_oracle_pure (a : A) (s : unit) :
  (simulate ⟪o⟫ (pure a) s).support = {(a, ())} := by simp [punit_eq s ()]

@[simp]
lemma support_simulate_stateless_oracle_bind (oa : oracle_comp spec A)
  (ob : A → oracle_comp spec B) (s : unit) :
  (simulate ⟪o⟫ (oa >>= ob) s).support =
    ⋃ (x : A × unit) (hx : x ∈ (simulate ⟪o⟫ oa ()).support),
      (simulate ⟪o⟫ (ob x.1) x.2).support :=
begin
  refine s.rec _,
  refine (set.ext $ λ y, _),
  simp,
  sorry,
end

@[simp]
lemma support_simulate_stateless_oracle_query (i : spec.ι) (t : spec.domain i) (s : unit) :
  (simulate ⟪o⟫ (query i t) s).support = {x | x.1 ∈ (o i t).support} :=
begin
  refine s.rec _,
  simp,
  sorry,
end

end simulate

section eval_distribution

lemma simulate_stateless_oracle_equiv_simulate' [spec'.finite_range] (s : unit) :
  simulate ⟪o⟫ oa s ≃ₚ (simulate' ⟪o⟫ oa s >>= λ a, pure (a, ())) :=
calc simulate ⟪o⟫ oa s ≃ₚ simulate ⟪o⟫ oa s >>= pure : symm (bind_pure_equiv _)
  ... ≃ₚ simulate ⟪o⟫ oa s >>= λ x, pure (x.1, x.2) : by simp only [prod.mk.eta]
  ... ≃ₚ simulate ⟪o⟫ oa s >>= λ x, pure (x.1, ()) : 
    bind_equiv_of_equiv_second _ (λ x, by simp [punit_eq x.snd ()])
  ... ≃ₚ simulate' ⟪o⟫ oa s >>= λ a, pure (a, ()) : by rw [simulate', bind_map_equiv]

lemma simulate'_stateless_oracle_equiv_of_oracle_equiv [spec'.finite_range] [spec''.finite_range] 
  {o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)}
  {o' : Π (i : spec.ι), spec.domain i → oracle_comp spec'' (spec.range i)}
  (s : unit) (h : ∀ (i : spec.ι) (t : spec.domain i), o i t ≃ₚ o' i t) :
  simulate' ⟪o⟫ oa s ≃ₚ simulate' ⟪o'⟫ oa s :=
begin
  induction oa with A a A B oa ob hoa hob i t generalizing s,
  { simp only [pure'_eq_pure, simulate'_pure, pure_map_equiv, eval_distribution_return] },
  { calc simulate' ⟪o⟫ (oa >>= ob) s
      ≃ₚ simulate ⟪o⟫ oa s >>= λ x, simulate' ⟪o⟫ (ob x.1) x.2 : simulate'_bind_equiv ⟪o⟫ oa ob _
      ... ≃ₚ simulate ⟪o'⟫ oa s >>= λ x, simulate' ⟪o'⟫ (ob x.1) x.2 : begin
        simp [simulate_stateless_oracle_equiv_simulate', hoa],
        congr,
        simpa [hob],
      end
      ... ≃ₚ simulate' ⟪o'⟫ (oa >>= ob) s : symm (simulate'_bind_equiv ⟪o'⟫ oa ob _) },
  { simp_rw [simulate'_query_equiv, stateless_oracle_apply, fst_map_bind_mk_equiv],
    exact map_equiv_of_equiv _ _ id (h i t) }
end 

lemma simulate'_stateless_oracle_query_equiv [spec.finite_range] (s : unit) :
  simulate' ⟪query⟫ oa s ≃ₚ oa :=
simulate'_tracking_oracle_query_equiv _ _ _ _

lemma simulate'_stateless_oracle_query_equiv_of_equiv [spec.finite_range] [spec'.finite_range] (s : unit)
  (ho : ∀ (i : spec.ι) (t : spec.domain i), o i t ≃ₚ query i t) :
  simulate' ⟪o⟫ oa s ≃ₚ oa :=
calc simulate' ⟪o⟫ oa s ≃ₚ simulate' ⟪query⟫ oa s
    : simulate'_stateless_oracle_equiv_of_oracle_equiv oa s ho
  ... ≃ₚ oa : simulate'_stateless_oracle_query_equiv oa s

end eval_distribution