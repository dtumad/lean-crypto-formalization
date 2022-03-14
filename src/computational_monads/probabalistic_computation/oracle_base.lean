import data.fintype.card
import measure_theory.probability_mass_function.constructions
import computational_monads.probabalistic_computation.oracle_comp_spec

open oracle_comp_spec

/-- TODO: docs

Semantically, `repeat oa p` represents a procedure like: `while (a ∉ p) {a ← oa}; return a`.
Simulation semantics can be defined for this, although repeated simulation may not be terminating.

Probability distribution semantics are harder, since if `p` always fails there will be no output.
To solve this, let `repeatₙ oa p` be the procedure that makes at most `n` loops before stopping.
Note that if `p` never holds on the output of `oa`, we have `repeatₙ oa p ≃ oa` for all `n`, 
`repeat oa p` then semantically represents the limit of `repeatₙ oa p` as `n → ∞`.
Note that in the case where the oracle is just a tape of random bits,
  the distribution of `repeatₙ` get arbitrarily close to that of `repeat` as `n → ∞`.

Note that time-complexity semantics don't assume `repeat oa p` is polynomial time,
so it can't be used in a polynomial-time reduction, unless that is taken as an additional axiom.
However it is still usable for describing security games and definitions of correctness. -/
inductive oracle_comp (spec : oracle_comp_spec) : Type → Type 1
| pure' (A : Type) (a : A) : oracle_comp A
| bind' (A B : Type) (oa : oracle_comp A) (ob : A → oracle_comp B) : oracle_comp B
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

instance oracle_comp.monad (spec : oracle_comp_spec) : monad (oracle_comp spec) :=
{ pure := oracle_comp.pure', bind := oracle_comp.bind' }

namespace oracle_comp

def coin : oracle_comp coin_oracle bool := query () ()

def uniform_fin (n : ℕ) : oracle_comp uniform_selecting (fin $ n + 1) := query n ()

notation `$[0..` n `]` := uniform_fin n

/-- Set of possible outputs of the computation, allowing for any possible output for the queries. -/
def support {spec : oracle_comp_spec} : Π {A : Type} (oa : oracle_comp spec A), set A
| _ (pure' A a) := {a}
| _ (bind' A B ca cb) := ⋃ a ∈ support ca, support (cb a)
| _ (query i t) := ⊤

section sim

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle -/
structure simulation_oracle (spec spec' : oracle_comp_spec) :=
(S : Type)
(o (i : spec.ι) (t : spec.domain i) (s : S) : oracle_comp spec' (spec.range i × S))

def identity_simulation_oracle (spec : oracle_comp_spec) : simulation_oracle spec spec :=
{ S := unit,
  o := λ i t _, query i t >>= λ u, return (u, ()) }

def logging_simulation_oracle (spec : oracle_comp_spec) : simulation_oracle spec spec :=
{ S := list (Σ (i : spec.ι), spec.domain i × spec.range i),
  o := λ i t log, query i t >>= λ u, return (u, ⟨i, t, u⟩ :: log) }

def query_cache (spec : oracle_comp_spec) : Type :=
list (Σ (i : spec.ι), spec.domain i × spec.range i)

def query_cache.lookup (spec : oracle_comp_spec) [spec.computable] (i : spec.ι) (t : spec.domain i) :
  query_cache spec → option (spec.range i)
| (⟨i', t', u⟩ :: log) := if hi : i' = i
  then if t = hi.rec_on t'
  then hi.rec_on (some u)
  else query_cache.lookup log
  else query_cache.lookup log
| [] := none

def caching_simulation_oracle (spec : oracle_comp_spec) [spec.computable] : simulation_oracle spec spec :=
{ S := query_cache spec,
  o := λ i t log, match query_cache.lookup spec i t log with
  | (some u) := return (u, log)
  | none := do { u ← query i t, return (u, ⟨i, t, u⟩ :: log) }
  end }

def simulation_oracle_append (spec₁ spec₂ spec' : oracle_comp_spec)
  (so : simulation_oracle spec₁ spec') (so' : simulation_oracle spec₂ spec') :
  simulation_oracle (spec₁ ++ spec₂) spec' :=
{ S := so.S × so'.S,
  o := λ i, match i with
  | sum.inl i := λ t s, do { ⟨u, s'⟩ ← so.o i t s.1, return (u, s', s.2) }
  | sum.inr i := λ t s, do { ⟨u, s'⟩ ← so'.o i t s.2, return (u, s.1, s') }
  end }

/-- Simulate an oracle comp to an oracle comp with a different spec.
  Requires providing a maximum recursion depth for the `repeat` constructor -/
def simulate {spec spec' : oracle_comp_spec} (sim_oracle : simulation_oracle spec spec') :
  Π {A : Type} (oa : oracle_comp spec A), sim_oracle.S → oracle_comp spec' (A × sim_oracle.S)
| _ (pure' A a) state := return ⟨a, state⟩
| _ (bind' A B oa ob) state := simulate oa state >>= λ ⟨a, state'⟩, simulate (ob a) state'
| _ (query i t) state := sim_oracle.o i t state

end sim

section eval_dist

-- Big step semantics for a computation with finite range oracles
-- The result of queries is assumed to be uniform over the oracle's codomain
-- Usually the `spec` when calling this will just be `unit →ₒ bool` (i.e. a tape of random bits),
-- However it can be any more general things as well, e.g. uniform sampling from finite sets

-- For `repeat oa p`, we filter the distribution by `p`, unless this filters everything,
-- in which case we instead keep the original distribution for `oa`.
-- This represents the limit of the distribution as the number of allowed loops goes to `∞`
private noncomputable def eval_dist {spec : oracle_comp_spec} [spec.computable] [spec.finite_range] :
  Π {A : Type} (oa : oracle_comp spec A),
    Σ (pa : pmf A), plift (pa.support = oa.support)
| _ (pure' A a) := ⟨pmf.pure a, 
  plift.up $ (pmf.support_pure a)⟩
| _ (bind' A B oa ob) := 
  let pa := eval_dist oa in
  let pb := λ a, eval_dist (ob a) in
  ⟨pa.1 >>= (λ a, (pb a).1), begin
    refine plift.up (set.ext $ λ b, _),
    erw pmf.mem_support_bind_iff pa.1,
    simp only [support, plift.down pa.2, set.mem_Union],
    split; rintro ⟨a, ha, ha'⟩; refine ⟨a, ha, _⟩; simpa [(plift.down (pb a).2)] using ha'
  end⟩
| _ (query i t) := ⟨pmf.uniform_of_fintype (spec.range i),
  plift.up ((pmf.support_uniform_of_fintype (spec.range i)))⟩

noncomputable def eval_distribution {A : Type} {spec : oracle_comp_spec}
  [spec.computable] [spec.finite_range] (oa : oracle_comp spec A) : pmf A :=
(eval_dist oa).1

notation `⟦` oa `⟧` := eval_distribution oa

lemma support_eval_distribution {A : Type} {spec : oracle_comp_spec} [spec.computable] [spec.finite_range]
  (oa : oracle_comp spec A) : ⟦oa⟧.support = oa.support :=
plift.down (eval_dist oa).2

-- TODO: Should this be an actual definition? or is notation easier?
notation oa `≃ₚ` oa' := ⟦oa⟧ = ⟦oa'⟧

end eval_dist

end oracle_comp