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

/-- TODO: could instead simp everything into `return` and `>>=`? -/
@[simp]
lemma pure_eq_pure' {A : Type} (spec : oracle_comp_spec) (a : A) :
  (pure a : oracle_comp spec A) = pure' A a := rfl

@[simp]
lemma return_eq_pure' {A : Type} (spec : oracle_comp_spec) (a : A) :
  (return a : oracle_comp spec A) = pure' A a := rfl

@[simp]
lemma bind_eq_bind' {A B : Type} {spec : oracle_comp_spec}
  (ca : oracle_comp spec A) (cb : A → oracle_comp spec B) :
  (ca >>= cb) = bind' A B ca cb := rfl

section constructions

def coin : oracle_comp coin_oracle bool := query () ()

def uniform_fin (n : ℕ) :
  oracle_comp uniform_selecting (fin $ n + 1) := query n ()

notation `$[0..` n `]` := uniform_fin n

def uniform_select_vector {A : Type} {n : ℕ} (v : vector A (n + 1)) :
  oracle_comp uniform_selecting A := v.nth <$> $[0..n] 

def uniform_select_list {A : Type} : Π (xs : list A) (h : ¬ xs.empty),
  oracle_comp uniform_selecting A
| [] h := false.elim (h rfl)
| (x :: xs) _ := uniform_select_vector ⟨x :: xs, list.length_cons x xs⟩ 

noncomputable def uniform_select_finset {A : Type} (bag : finset A) (h : bag.nonempty) :
  oracle_comp uniform_selecting A := 
uniform_select_list (bag.to_list) (let ⟨x, hx⟩ := h in
  λ h', list.not_mem_nil x ((list.empty_iff_eq_nil.1 h') ▸ (finset.mem_to_list bag).2 hx))

noncomputable def uniform_select_fintype {A : Type} [fintype A] [nonempty A] :
  oracle_comp uniform_selecting A :=
uniform_select_finset ⊤ finset.univ_nonempty

end constructions

section support

/-- Set of possible outputs of the computation, allowing for any possible output of the queries. -/
def support {spec : oracle_comp_spec} : Π {A : Type} (oa : oracle_comp spec A), set A
| _ (pure' A a) := {a}
| _ (bind' A B ca cb) := ⋃ a ∈ ca.support, (cb a).support
| _ (query i t) := ⊤

@[simp]
lemma support_pure' {A : Type} (spec : oracle_comp_spec) (a : A) :
  (pure' A a : oracle_comp spec A).support = {a} := rfl

-- @[simp]
-- lemma support_pure {A : Type} (spec : oracle_comp_spec) (a : A) :
--   (pure a : oracle_comp spec A).support = {a} := by simp

-- @[simp]
-- lemma support_return {A : Type} (spec : oracle_comp_spec) (a : A) :
--   (return a : oracle_comp spec A).support = {a} := by simp

@[simp]
lemma support_bind' {A B : Type} {spec : oracle_comp_spec}
  (ca : oracle_comp spec A) (cb : A → oracle_comp spec B) :
  (bind' A B ca cb).support = ⋃ a ∈ ca.support, (cb a).support := rfl

@[simp]
lemma support_query {spec : oracle_comp_spec} (i : spec.ι) (t : spec.domain i) :
  (query i t : oracle_comp spec (spec.range i)).support = ⊤ := rfl

end support

section simulate

/-- Specifies a way to simulate a set of oracles using another set of oracles. 
  e.g. using uniform random selection to simulate a hash oracle -/
structure simulation_oracle (spec spec' : oracle_comp_spec) :=
(S : Type)
(o (i : spec.ι) (t : spec.domain i) (s : S) : oracle_comp spec' (spec.range i × S))

/-- Simulate an oracle comp to an oracle comp with a different spec.
  Requires providing a maximum recursion depth for the `repeat` constructor -/
def simulate {spec spec' : oracle_comp_spec} (sim_oracle : simulation_oracle spec spec') :
  Π {A : Type} (oa : oracle_comp spec A), sim_oracle.S → oracle_comp spec' (A × sim_oracle.S)
| _ (pure' A a) state := return ⟨a, state⟩
| _ (bind' A B oa ob) state := do { ⟨a, state'⟩ ← simulate oa state, simulate (ob a) state' }
| _ (query i t) state := sim_oracle.o i t state

/-- Get the result of simulation without returning the internal oracle state -/
def simulate' {spec spec' : oracle_comp_spec} (sim_oracle : simulation_oracle spec spec') 
  {A : Type} (oa : oracle_comp spec A) (s : sim_oracle.S) :
  oracle_comp spec' A :=
prod.fst <$> oa.simulate sim_oracle s

end simulate

/-- Oracle computations that uniformly make at most a given number of queries.
  In particular `simulate` will always the `simulation_oracle` at most that many times -/
inductive queries_at_most {spec : oracle_comp_spec} : 
  Π {A : Type}, oracle_comp spec A → ℕ → Type 1
| queries_at_most_sample {A : Type} (a : A) :
    queries_at_most (pure' A a) 0
| queries_at_most_bind' {A B : Type} (ca : oracle_comp spec A) (cb : A → oracle_comp spec B)
    (p q : ℕ) (hca : queries_at_most ca p) (hcb : ∀ a, queries_at_most (cb a) q) :
    queries_at_most (bind' A B ca cb) (p + q)
| queries_at_most_query {i : spec.ι} (a : spec.domain i) :
    queries_at_most (query i a) 1 

def count_oracle_queries {spec : oracle_comp_spec} :
  simulation_oracle spec spec :=
{ S := ℕ,
  o := λ i t n, do { u ← query i t, return ⟨u, n + 1⟩ } }

/-- Soundness of `queries_at_most` with respect to simulation -/
theorem qam {spec spec' : oracle_comp_spec} {A : Type} (oa : oracle_comp spec A)
  (x : A × ℕ) (hx : x ∈ (simulate count_oracle_queries oa nat.zero).support)
  (n : ℕ) (hn : queries_at_most oa n) : x.2 ≤ n :=
sorry

end oracle_comp