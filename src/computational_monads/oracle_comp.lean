import data.fintype.card
import measure_theory.probability_mass_function.constructions
import computational_monads.oracle_comp_spec

variables {A B : Type} {spec : oracle_comp_spec}

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

/-- TODO: could instead simp everything into `return` and `>>=`? -/
@[simp]
lemma pure_eq_pure' (spec : oracle_comp_spec) (a : A) :
  (pure a : oracle_comp spec A) = pure' A a := rfl

@[simp]
lemma return_eq_pure' (spec : oracle_comp_spec) (a : A) :
  (return a : oracle_comp spec A) = pure' A a := rfl

@[simp]
lemma bind_eq_bind' (ca : oracle_comp spec A) (cb : A → oracle_comp spec B) :
  (ca >>= cb) = bind' A B ca cb := rfl

section support

/-- Set of possible outputs of the computation, allowing for any possible output of the queries. -/
def support {spec : oracle_comp_spec} : Π {A : Type} (oa : oracle_comp spec A), set A
| _ (pure' A a) := {a}
| _ (bind' A B ca cb) := ⋃ a ∈ ca.support, (cb a).support
| _ (query i t) := ⊤

@[simp]
lemma support_pure' {A : Type} (spec : oracle_comp_spec) (a : A) :
  (pure' A a : oracle_comp spec A).support = {a} := rfl

lemma support_pure {A : Type} (spec : oracle_comp_spec) (a : A) :
  (pure a : oracle_comp spec A).support = {a} := by simp

lemma support_return {A : Type} (spec : oracle_comp_spec) (a : A) :
  (return a : oracle_comp spec A).support = {a} := by simp

@[simp]
lemma support_bind' {A B : Type} {spec : oracle_comp_spec}
  (ca : oracle_comp spec A) (cb : A → oracle_comp spec B) :
  (bind' A B ca cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

lemma support_bind {A B : Type} {spec : oracle_comp_spec}
  (ca : oracle_comp spec A) (cb : A → oracle_comp spec B) :
  (ca >>= cb).support = ⋃ a ∈ ca.support, (cb a).support := by simp

@[simp]
lemma support_query {spec : oracle_comp_spec} (i : spec.ι) (t : spec.domain i) :
  (query i t : oracle_comp spec (spec.range i)).support = ⊤ := rfl

end support

section simulate

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle -/
structure simulation_oracle (spec spec' : oracle_comp_spec) :=
(S : Type)
(o (i : spec.ι) : (spec.domain i × S) → oracle_comp spec' (spec.range i × S))

/-- Simulate an oracle comp to an oracle comp with a different spec.
  Requires providing a maximum recursion depth for the `repeat` constructor -/
def simulate {spec spec' : oracle_comp_spec} (sim_oracle : simulation_oracle spec spec') :
  Π {A : Type} (oa : oracle_comp spec A), sim_oracle.S → oracle_comp spec' (A × sim_oracle.S)
| _ (pure' A a) state := return ⟨a, state⟩
| _ (bind' A B oa ob) state := do { ⟨a, state'⟩ ← simulate oa state, simulate (ob a) state' }
| _ (query i t) state := sim_oracle.o i (t, state)

/-- Get the result of simulation without returning the internal oracle state -/
def simulate' {spec spec' : oracle_comp_spec} (sim_oracle : simulation_oracle spec spec') 
  {A : Type} (oa : oracle_comp spec A) (s : sim_oracle.S) :
  oracle_comp spec' A :=
prod.fst <$> oa.simulate sim_oracle s

end simulate

end oracle_comp