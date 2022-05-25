import computational_monads.constructions.uniform_select
import computational_monads.simulation_semantics.simulate
import computational_monads.simulation_semantics.stateless_oracle

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

section query_log

-- log by keeping a list for each of the indexed oracles
-- TODO: this version seems to work a lot better. For complexity stuff can maybe axiomatize
def query_log' (spec : oracle_spec) : Type :=
  Π (i : spec.ι), list (spec.domain i × spec.range i)

-- log with no entries for any of the oracles
def query_log'.init (spec : oracle_spec) : query_log' spec :=
λ i, []

-- remove the head of the index `i` log
def query_log'.remove_head [spec.computable]
  (log : query_log' spec) (i : spec.ι) : query_log' spec :=
λ i', if i' = i then (log i').tail else (log i')

def query_log'.lookup [spec.computable]
  (log : query_log' spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) :=
((log i).find $ (= t) ∘ prod.fst).map prod.snd

-- Different lookup that only looks at head, and removes the element from the cache
def query_log'.lookup_fst [spec.computable]
  (log : query_log' spec) (i : spec.ι) (t : spec.domain i) :
  option (spec.range i) × query_log' spec :=
begin
  refine match (log i).nth 0 with
  | none := (none, query_log'.init spec)
  | some ⟨t', u⟩ := if t' = t then (some u, log.remove_head i)
                    else (none, query_log'.init spec) -- TODO: maybe don't clear everything here?
  end
end

-- TODO: this might work better as a function type? (above ↑)
def query_log (spec : oracle_spec) : Type :=
list (Σ (i : spec.ι), spec.domain i × spec.range i)

namespace query_log

/-- Looking up a cache value requires use of the first equality condition
  to make the following conditions and return values type correct. -/
def lookup {spec : oracle_spec} [spec.computable] :
  Π (log : query_log spec) (i : spec.ι) (t : spec.domain i), option (spec.range i)
| (⟨i', t', u⟩ :: log) i t := if hi : i' = i
    then (if t = hi.rec_on t' then hi.rec_on (some u)
    else lookup log i t) else lookup log i t
| [] i t := none

/-- Like `lookup-/
def query_log.lookup_head {spec : oracle_spec} [spec.computable] :
  Π (log : query_log spec) (i : spec.ι) (t : spec.domain i), (option $ spec.range i) × query_log spec :=
sorry

end query_log

end query_log

section logging_oracle

/-- Extend the state of a simulation oracle to also track the inputs and outputs of queries.
  The actual oracle calls are forwarded directly to the original oracle. -/
def logging_simulation_oracle (spec : oracle_spec) : 
  simulation_oracle spec spec :=
{ S := query_log spec,
  o := λ i ⟨t, log⟩, do { u ← query i t, return (u, ⟨i, t, u⟩ :: log) } }

namespace logging_simulation_oracle

@[simp]
lemma simulate_pure (a : A) (log : query_log spec) :
  simulate (logging_simulation_oracle _) (return a) log = return ⟨a, log⟩ :=
rfl

@[simp]
lemma simulate_query (i : spec.ι) (t : spec.domain i) (log : query_log spec) :
  simulate (logging_simulation_oracle _) (query i t) log =
    do { u ← query i t, return (u, ⟨i, t, u⟩ :: log) } :=
rfl

@[simp]
lemma simulate_bind (oa : oracle_comp spec A) (ob : A → oracle_comp spec B) (log : query_log spec) :
  simulate (logging_simulation_oracle _) (oa >>= ob) log =
    (simulate (logging_simulation_oracle _) oa log) >>=
      (λ x, simulate (logging_simulation_oracle _) (ob x.1) x.2) :=
rfl

@[simp]
lemma eval_distribution_fst_simulate [spec.finite_range] (oa : oracle_comp spec A) (log : query_log spec) :
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
  o := λ i ⟨t, seed⟩, match seed with
  | ⟨i', t', u⟩ :: seed := if hi : i = i'
    then begin
      induction hi,
      refine if t = t' then (return (u, seed))
        else (do {u ← query i t, return (u, [])}),
    end
    else do { u ← query i t, return (u, []) }
  | [] := do {u ← query i t, return (u, []) }
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
  | none := do { u ← query i t, return (u, ⟨i, t, u⟩ :: log) }
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
