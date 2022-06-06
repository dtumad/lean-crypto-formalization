import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.stateless_oracle
import computational_monads.simulation_semantics.constructions.query_log

open oracle_comp oracle_spec

variables {spec spec' spec'' : oracle_spec} {A B C : Type}

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

/-- Use the first element of the `seed` as the query result if inputs match.
  If the query values don't match then throw away the seed as computation has diverged.
  Using this with a log from a previous computation ensures they behave identically. -/
def seeded_simulation_oracle (spec : oracle_spec) [computable spec] :
  simulation_oracle spec spec :=
{ S := query_log spec,
  o := λ i ⟨t, seed⟩, match seed.lookup_fst i t with
    | none := functor.map (λ u, (u, query_log.init spec)) (query i t)
    | (some u) := return (u, seed.remove_head i)
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