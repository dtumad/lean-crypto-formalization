import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.stateless_oracle
import computational_monads.simulation_semantics.constructions.query_log


open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}

section compose

def oracle_compose {spec spec' spec'' : oracle_spec}
  (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'') :
  simulation_oracle spec spec'' :=
{ S := so.S × so'.S,
  o := λ i ⟨t, s, s'⟩, simulate so' (so.o i (t, s)) s' >>= λ ⟨⟨u, s⟩, s'⟩, return (u, s, s') }

notation so' `∘ₛ` so := oracle_compose so so'

variables (so : simulation_oracle spec spec') (so' : simulation_oracle spec' spec'')

end compose

section logging_oracle

/-- Extend the state of a simulation oracle to also track the inputs and outputs of queries.
  The actual oracle calls are forwarded directly to the original oracle. -/
def logging_simulation_oracle (spec : oracle_spec) [spec.computable] : 
  simulation_oracle spec spec :=
{ S := query_log spec,
  o := λ i ⟨t, log⟩, do { u ← query i t, return (u, log.log_query i t u) } }

namespace logging_simulation_oracle

@[simp]
lemma simulate_pure [spec.computable] (a : A) (log : query_log spec) :
  simulate (logging_simulation_oracle _) (return a) log = return ⟨a, log⟩ :=
rfl

@[simp]
lemma simulate_query [spec.computable] (i : spec.ι) (t : spec.domain i) (log : query_log spec) :
  simulate (logging_simulation_oracle _) (query i t) log =
    do { u ← query i t, return (u, log.log_query i t u) } :=
rfl

@[simp]
lemma simulate_bind [spec.computable] (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (log : query_log spec) :
  simulate (logging_simulation_oracle _) (oa >>= ob) log =
    (simulate (logging_simulation_oracle _) oa log) >>=
      (λ x, simulate (logging_simulation_oracle _) (ob x.1) x.2) :=
rfl

@[simp]
lemma eval_distribution_fst_simulate [spec.computable] [spec.finite_range] (oa : oracle_comp spec A) (log : query_log spec) :
  ⟦ (simulate (logging_simulation_oracle _) oa log) >>= (λ a, return a.1) ⟧ = ⟦ oa ⟧ :=
begin
  induction oa,
  {
    simp,
    refine (pmf.pure_bind _ _).trans _,
    simp,
  },
  {
    sorry,
  },
  {
    sorry
  }
end

end logging_simulation_oracle

end logging_oracle

section seeded_oracle

def seeded_simulation_oracle (spec : oracle_spec) [computable spec] :
  simulation_oracle spec spec :=
{ S := query_log spec,
  o := λ i ⟨t, seed⟩, begin
    refine let ⟨u', seed⟩ := seed.take_fst i t in match u' with
    | none := do { u ← query i t, return (u, seed) }
    | (some u) := return (u, seed)
    end
  end }

namespace seeded_simulation_oracle

end seeded_simulation_oracle

end seeded_oracle

section caching_oracle

-- TODO: make this a extension property instead.
def caching_simulation_oracle (spec : oracle_spec) [spec.computable] :
  simulation_oracle spec spec :=
{ S := query_log spec,
  o := λ i ⟨t, log⟩, match log.lookup i t with
  | (some u) := return (u, log) -- Return the cached value if it already exists
  | none := do { u ← query i t, return (u, log.log_query i t u) }
  end }

end caching_oracle

section oracle_append

def simulation_oracle_append (spec₁ spec₂ spec' : oracle_spec)
  (so : simulation_oracle spec₁ spec') (so' : simulation_oracle spec₂ spec') :
  simulation_oracle (spec₁ ++ spec₂) spec' :=
{ S := so.S × so'.S,
  o := λ i, match i with
  | sum.inl i := λ ⟨t, s⟩, do { ⟨u, s'⟩ ← so.o i ⟨t, s.1⟩, return (u, s', s.2) }
  | sum.inr i := λ ⟨t, s⟩, do { ⟨u, s'⟩ ← so'.o i ⟨t, s.2⟩, return (u, s.1, s') }
  end }

notation so `⟪++⟫` so' := simulation_oracle_append _ _ _ so so'

noncomputable example : simulation_oracle (coin_oracle ++ uniform_selecting) uniform_selecting :=
random_simulation_oracle coin_oracle ⟪++⟫ identity_oracle uniform_selecting

end oracle_append

section simulate_sides

def simulate_right {spec spec' : oracle_spec}
  (so : simulation_oracle spec' spec) :
  simulation_oracle (spec ++ spec') spec :=
identity_oracle spec ⟪++⟫ so

end simulate_sides
