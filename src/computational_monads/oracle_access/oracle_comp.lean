import computational_monads.probabalistic_computation.constructions

variables {C D : Type}

structure oracle_comp_spec : Type 1 := 
(ι : Type)
(ι_decidable_eq : decidable_eq ι)
(domain range : ι → Type)

/-- `oracle_comp oracle_spec C` is a probablistic computation of a value in `C`,
  with access to oracles (specified by `oracle_spec`) via the `query` constructor.
  The oracle's semantics aren't specified until evaluation (`simulate`),
    since algorithm specification only needs to know the types of queries, not the values.
  TODO: Add back `run` constructor to convert between oracles (or construct it manually) -/
inductive oracle_comp (spec : oracle_comp_spec) : Type → Type 1
| sample {C : Type} (c : prob_comp C) : oracle_comp C
| bind' (C D : Type) (oc : oracle_comp C) (od : C → oracle_comp D) : oracle_comp D
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

namespace oracle_comp

section oracle_comp_spec

instance oracle_comp_spec.ι_decidable_eq {spec : oracle_comp_spec} :
  decidable_eq (spec.ι) := spec.ι_decidable_eq

/-- No access to any oracles -/
def empty_spec : oracle_comp_spec :=
{ ι := empty,
  ι_decidable_eq := decidable_eq_of_subsingleton,
  domain := empty.elim,
  range := empty.elim }

/-- Access to a single oracle `T → U` -/
def singleton_spec (T U : Type) : oracle_comp_spec :=
{ ι := unit,
  ι_decidable_eq := decidable_eq_of_subsingleton,
  domain := λ _, T,
  range := λ _, U }

notation `⟦` T `→ᵒ` U `⟧` := singleton_spec T U

example (T U : Type) : oracle_comp_spec := ⟦T →ᵒ U⟧

/-- Combine two specifications using a `sum` type to index the different specs -/
instance has_append : has_append oracle_comp_spec :=
{ append := λ spec spec', 
  { ι := spec.ι ⊕ spec'.ι,
    ι_decidable_eq := @sum.decidable_eq spec.ι spec.ι_decidable_eq spec'.ι spec'.ι_decidable_eq,
    domain := sum.elim spec.domain spec'.domain,
    range := sum.elim spec.range spec'.range } }

end oracle_comp_spec 

section monad

@[simps]
instance monad (spec : oracle_comp_spec) :
  monad (oracle_comp spec) :=
{ pure := λ C c, oracle_comp.sample (return c),
  bind := oracle_comp.bind' }

@[simp]
lemma return_eq_sample {spec : oracle_comp_spec} (c : C) :
  (return c : oracle_comp spec C) = sample (return c) := rfl

-- Example of accessing a pair of different oracles and passing
example {α β : Type} (ca : prob_comp α) (cb : prob_comp β) : 
  oracle_comp (⟦α →ᵒ C⟧ ++ ⟦β →ᵒ D⟧) (C × D) :=
do{ x ← sample ca, y ← sample cb,
    x' ← query (sum.inl ()) x,
    y' ← query (sum.inr ()) y,
    return (x', y') }

end monad

section query_log

/-- Type defining a log of oracle queries and the returned values,
  parameterized by the specification of the oracle access.
  Oracle simulation dracks this value automatically.
  TODO: does this work very well with computational complexity things? -/
def query_log (spec : oracle_comp_spec) : Type :=
Π (i : spec.ι), list (spec.domain i × spec.range i)

def log_query {spec : oracle_comp_spec} (log : query_log spec)
  (i : spec.ι) (t : spec.domain i) (u : spec.range i) : query_log spec :=
λ i', if hi : i = i' then ⟨hi.rec_on t, hi.rec_on u⟩ :: log i' else log i'

def get_output {spec : oracle_comp_spec} (log : query_log spec)
  (i : spec.ι) [decidable_eq $ spec.domain i] (t : spec.domain i) : 
  option (spec.range i) :=
option.map prod.snd ((log i).find ((=) t ∘ prod.fst))

end query_log

section simulation_oracle

/-- Specifies a method for simulating an oracle for the given `oracle_comp_spec`,
  Where `S` is the type of the oracle's internal state and `o` simulates the oracle given a current state,
  eventually returning a query result and an updated state value. -/
structure simulation_oracle (spec : oracle_comp_spec) : Type 1 :=
(S : Type)
(o : Π (i : spec.ι), spec.domain i → S → prob_comp (spec.range i × S))

/-- Combine simultation oracles two get a simulation oracle on the appended `spec`,
  using a product type to track internal states of both oracles -/
def simulation_oracle.append {spec spec' : oracle_comp_spec}
  (so : simulation_oracle spec) (so' : simulation_oracle spec') :
  simulation_oracle (spec ++ spec') :=
{ S := so.S × so'.S,
  o := λ i, match i with
    | (sum.inl i) := λ x ⟨s, s'⟩, do{ (y, s) ← (so.o i x s), return (y, ⟨s, s'⟩) }
    | (sum.inr i) := λ x ⟨s, s'⟩, do{ (y, s') ← (so'.o i x s'), return (y, ⟨s, s'⟩) }
  end }

/-- Return random values for any new query, returning the same value for repeated queries -/
@[simps]
def random_oracle (T U : Type) 
  [decidable_eq T] [fintype U] [nonempty U] :
  simulation_oracle ⟦T →ᵒ U⟧ :=
{ S := list (T × U),
  o := λ _ t log, match (log.find ((= t) ∘ prod.fst)) with
    | none := prob_comp.uniform (⊤ : finset U) (finset.univ_nonempty)
                >>= (λ u, return ⟨u, ⟨t, u⟩ :: log⟩)
    | (some ⟨t, u⟩) := return ⟨u, log⟩
  end }

/-- Construct a simulation oracle from a stateless function,
  using internal state to log queries to the oracle -/
def logging_simulation_oracle {C : Type} {spec : oracle_comp_spec}
  (oc : oracle_comp spec C)
  (o : Π (i : spec.ι), spec.domain i → prob_comp (spec.range i)) :
  simulation_oracle spec :=
{ S := list (Σ (i : spec.ι), spec.domain i),
  o := λ t a as, do { b ← o t a, return (b, ⟨t, a⟩ :: as) } }

end simulation_oracle

section simulate

/-- Evaluation distribution of an `oracle_comp A B C` as a `prob_comp A`.
`S` is the type of the internal state of the `A` to `B` oracle, and `s` is the initial state.
`o` takes the current oracle state and an `A` value, and computes a `B` value and new oracle state. -/
def simulate {spec : oracle_comp_spec} (so : simulation_oracle spec) : 
  Π {C : Type} (oc : oracle_comp spec C) (s : so.S), prob_comp (C × so.S)
| C (sample c) s := do {x ← c, return (x, s)}
| C (bind' _ D oc od) s := do{⟨c, s'⟩ ← simulate oc s, simulate (od c) s'}
| C (query i a) s := so.o i a s

@[simp]
def simulate_result {C : Type} {spec : oracle_comp_spec} (so : simulation_oracle spec) (s : so.S) 
  (oc : oracle_comp spec C) : prob_comp C :=
functor.map prod.fst (simulate so oc s)

@[simp]
lemma simulate_query {spec : oracle_comp_spec} (so : simulation_oracle spec)
  {i : spec.ι} (a : spec.domain i) (s : so.S) :
  (query i a : oracle_comp spec (spec.range i)).simulate so s = so.o i a s := 
rfl

@[simp]
lemma simulate_sample {spec : oracle_comp_spec} (so : simulation_oracle spec)
  {C : Type} (c : prob_comp C) (s : so.S) :
  simulate so (sample c) s = do {x ← c, return (x, s)} :=
rfl

@[simp]
lemma simulate_bind' {spec : oracle_comp_spec} (so : simulation_oracle spec)
  {C D : Type} (oc : oracle_comp spec C) 
  (od : C → oracle_comp spec D) (s : so.S) :
  simulate so (bind' C D oc od) s = 
    do {⟨c, s⟩ ← simulate so oc s, simulate so (od c) s} :=
congr_arg (λ x, simulate so oc s >>= x) (funext $ prod.rec $ by simp [simulate])

lemma simulate_bind {spec : oracle_comp_spec} (so : simulation_oracle spec)
  {C D : Type} (oc : oracle_comp spec C)
  (od : C → oracle_comp spec D) (s : so.S) :
  simulate so (oc >>= od) s =
    do {(c, s') ← simulate so oc s, simulate so (od c) s'} :=
simulate_bind' so oc od s

end simulate

section queries_at_most

inductive queries_at_most {spec : oracle_comp_spec} : 
  Π {A : Type}, oracle_comp spec A → ℕ → Type 1
| queries_at_most_sample {A : Type} (ca : prob_comp A) :
    queries_at_most (sample ca) 0
| queries_at_most_bind' {A B : Type} (ca : oracle_comp spec A) (cb : A → oracle_comp spec B)
    (p q : ℕ) (hca : queries_at_most ca p) (hcb : ∀ a, queries_at_most (cb a) q) :
    queries_at_most (bind' A B ca cb) (p + q)
| queries_at_most_query {i : spec.ι} (a : spec.domain i) :
    queries_at_most (query i a) 1

end queries_at_most

end oracle_comp