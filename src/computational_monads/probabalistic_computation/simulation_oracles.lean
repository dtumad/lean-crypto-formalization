import computational_monads.probabalistic_computation.oracle_base

open oracle_comp oracle_comp_spec

section stateless_oracles

def stateless_simulation_oracle (spec spec' : oracle_comp_spec)
  (o : Π (i : spec.ι), spec.domain i → oracle_comp spec' (spec.range i)) :
  simulation_oracle spec spec' :=
{ S := unit,
  o := λ i t _, o i t >>= λ u, return (u, ()) }

notation `⟪` o `⟫` := stateless_simulation_oracle _ _ o

def identity_simulation_oracle (spec : oracle_comp_spec) : simulation_oracle spec spec :=
⟪ query ⟫

noncomputable def random_simulation_oracle (spec : oracle_comp_spec) [spec.computable] [spec.finite_range] : 
  simulation_oracle spec uniform_selecting :=
⟪ λ i t, uniform_select_fintype ⟫

end stateless_oracles

section caching_oracles

def query_cache (spec : oracle_comp_spec) : Type :=
list (Σ (i : spec.ι), spec.domain i × spec.range i)

def logging_simulation_oracle (spec : oracle_comp_spec) : simulation_oracle spec spec :=
{ S := list (Σ (i : spec.ι), spec.domain i × spec.range i),
  o := λ i t log, query i t >>= λ u, return (u, ⟨i, t, u⟩ :: log) }

def query_cache.lookup (spec : oracle_comp_spec) [spec.computable] (i : spec.ι) (t : spec.domain i) :
  query_cache spec → option (spec.range i)
| (⟨i', t', u⟩ :: log) := if hi : i' = i
    then (if t = hi.rec_on t' then hi.rec_on (some u)
    else query_cache.lookup log) else query_cache.lookup log
| [] := none

def caching_simulation_oracle (spec : oracle_comp_spec) [spec.computable] :
  simulation_oracle spec spec :=
{ S := query_cache spec,
  o := λ i t log, match query_cache.lookup spec i t log with
  | (some u) := return (u, log)
  | none := do { u ← query i t, return (u, ⟨i, t, u⟩ :: log) }
  end }

end caching_oracles

section oracle_append

def simulation_oracle_append (spec₁ spec₂ spec' : oracle_comp_spec)
  (so : simulation_oracle spec₁ spec') (so' : simulation_oracle spec₂ spec') :
  simulation_oracle (spec₁ ++ spec₂) spec' :=
{ S := so.S × so'.S,
  o := λ i, match i with
  | sum.inl i := λ t s, do { ⟨u, s'⟩ ← so.o i t s.1, return (u, s', s.2) }
  | sum.inr i := λ t s, do { ⟨u, s'⟩ ← so'.o i t s.2, return (u, s.1, s') }
  end }

notation so `⟪++⟫` so' := simulation_oracle_append _ _ _ so so'

end oracle_append
