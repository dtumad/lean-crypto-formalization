import computational_monads.comp

/-!
# Model of Nondeterministic Computation With Oracles

This file extends the `comp` monad to allow compuation with oracle access.
The definition allows for oracles to hide their internal state,
  which wouldn't be possible by just giving the adversary an explicit function.
It also allows for definitions that inpect the inputs of calls made to the oracle,
  e.g. an `oracle_comp M S (M × S)` attempting to forge a signature on an unqueried message.
-/

structure oracle_comp_spec :=
(ι : Type)
(D R : ι → Type)

namespace oracle_comp_spec

def domain (spec : oracle_comp_spec)
  (i : spec.ι) : Type :=
spec.D i

def range (spec : oracle_comp_spec)
  (i : spec.ι) : Type :=
spec.R i

def empty_spec : oracle_comp_spec :=
{ ι := empty,
  D := empty.elim,
  R := empty.elim }

def singleton_spec (A B : Type) : oracle_comp_spec :=
{ ι := unit,
  D := λ _, A,
  R := λ _, B }

@[reducible]
instance has_append : has_append oracle_comp_spec :=
{ append := λ spec spec', 
  { ι := spec.ι ⊕ spec'.ι,
    D := sum.elim spec.D spec'.D,
    R := sum.elim spec.R spec'.R } } 

end oracle_comp_spec 

open oracle_comp_spec

/-- `oracle_comp A B C` is the type of a computation of a value of type `C`,
  with access to a family of oracle taking values in `A t` to values in `B t`.
  The oracle's semantics aren't specified until evaluation (`eval_distribution`),
    since algorithm specification only needs to know the types, not the values.
    
  The type `T` is used to index multiple oracles,
    e.g. taking `T := fin 2` gives access to two distinct oracles -/
inductive oracle_comp (spec : oracle_comp_spec) : Type → Type 1
| oc_ret {C : Type} (c : comp C) : oracle_comp C
| oc_bind {C D : Type} (oc : oracle_comp C) (od : C → oracle_comp D) : oracle_comp D
| oc_query (i : spec.ι) (a : spec.domain i) : oracle_comp (spec.range i)

@[simps]
instance oracle_comp.monad (spec : oracle_comp_spec) :
  monad (oracle_comp spec) :=
{ pure := λ C c, oracle_comp.oc_ret (comp.ret c), 
  bind := λ C D oc od, oc.oc_bind od }

@[simp]
lemma oracle_comp.return_eq (spec : oracle_comp_spec)
  {A : Type} (a : A) :
  (return a : oracle_comp spec A) = oracle_comp.oc_ret (comp.ret a) :=
rfl

-- Example of accessing a pair of different oracles
example (A B : Type) : 
  oracle_comp (singleton_spec ℕ A ++ singleton_spec ℤ B) (A × B) :=
do x ← oracle_comp.oc_ret (comp.rnd (fin 100)),
  x' ← oracle_comp.oc_query (sum.inl ()) x.val,
  y ← return (x : ℤ),
  y' ← oracle_comp.oc_query (sum.inr ()) y,
  return (x', y')

variables 

namespace oracle_comp

/-- Simulate an `A → B` oracle as an `A' → B'` oracle,
  using the stateful function `o` with initial state `s` -/
def oc_run {S : Type} (spec spec' : oracle_comp_spec) :
  Π {C : Type} (oc : oracle_comp spec C) (s : S)
    (o : Π t, S → spec.domain t → oracle_comp spec' (spec.range t × S)),
  oracle_comp spec' (C × S)
| _ (oc_query i a) s o := o i s a
| _ (oc_ret cc) s o := oc_ret (cc >>= λ c, return (c, s))
| _ (oc_bind oc od) s o := (oc_run oc s o) >>= (λ cs, oc_run (od cs.1) cs.2 o)

variables {spec : oracle_comp_spec} {C : Type}

/-- Every oracle_comp gives rise to a mapping from query assignments to the base comp type,
  where the value in `C` is the result of the computation if oracles behave like the input,
  and internal `comp` values return their base values -/
def oracle_comp_base_exists (oc : oracle_comp spec C) : (Π t, spec.D t → spec.R t) → C :=
oracle_comp.rec_on oc (λ C c _, comp.comp_base_exists c) 
  (λ C D oc od hoc hod o, hod (hoc o) o) (λ t a o, o t a)

section is_well_formed

@[class]
def is_well_formed : Π {C : Type}, oracle_comp spec C → Prop
| _ (oc_query i a) := true
| _ (oc_ret cc) := cc.is_well_formed
| _ (oc_bind oc od) := oc.is_well_formed ∧ ∀ c, (od c).is_well_formed

@[simp]
-- TODO: maybe `i` shouldn't be implicit anymore?
lemma oc_query_is_well_formed {i : spec.ι} (a : spec.domain i) :
  (oc_query i a : oracle_comp spec (spec.range i)).is_well_formed :=
true.intro

@[simp]
lemma oc_ret_is_well_formed_iff {C : Type} (c : comp C) :
  (oc_ret c : oracle_comp spec C).is_well_formed ↔ c.is_well_formed :=
iff.rfl

@[simp]
lemma oc_bind_is_well_formed_iff {C D : Type} 
  (oc : oracle_comp spec C) (od : C → oracle_comp spec D) :
  (oc_bind oc od).is_well_formed ↔
    oc.is_well_formed ∧ ∀ c, (od c).is_well_formed :=
iff.rfl

@[simp]
lemma oc_bind.is_well_formed_iff_left {C D : Type} (oc : oracle_comp spec C) (od : C → oracle_comp spec D)
  [hoc : is_well_formed oc] :
  (oc_bind oc od).is_well_formed ↔ (∀ c, (od c).is_well_formed) :=
by simp [hoc]

@[simp]
instance oc_query.is_well_formed {i : spec.ι} (a : spec.domain i) :
  (oc_query i a : oracle_comp spec (spec.range i)).is_well_formed :=
by simp

@[simp]
instance oc_ret.is_well_formed {C : Type} (cc : comp C) 
  [h : cc.is_well_formed] : (oc_ret cc : oracle_comp spec C).is_well_formed :=
by simp [h]

@[simp]
instance oc_bind.is_well_formed {C D : Type} (oc : oracle_comp spec C) (od : C → oracle_comp spec D)
  [hoc : is_well_formed oc] [hod : ∀ c, is_well_formed $ od c] :
  (oc_bind oc od).is_well_formed :=
by simp [hoc, hod]

lemma is_well_formed_of_oc_bind_left {C D : Type}
  {oc : oracle_comp spec C} {od : C → oracle_comp spec D} : 
  (oc >>= od).is_well_formed → oc.is_well_formed :=
λ h, h.1

lemma is_well_formed_of_oc_bind_right {C D : Type}
  {oc : oracle_comp spec C} {od : C → oracle_comp spec D} :
  (oc >>= od).is_well_formed → ∀ c, (od c).is_well_formed :=
λ h, h.2

end is_well_formed

/-- Specifies a method for simulating an oracle for the given `oracle_comp_spec`,
  Where `S` is the oracles internal state and `o` simulates the oracle given a current state,
  eventually returning an updated state value. -/
structure simulation_oracle (spec : oracle_comp_spec) :=
(S : Type)
(o : Π (i : spec.ι), S → spec.domain i → comp (spec.range i × S))
(oracle_is_well_formed (i : spec.ι) (s : S) (x : spec.domain i) :
  (o i s x).is_well_formed)

instance simulation_oracle.is_well_formed {spec : oracle_comp_spec}
  (so : simulation_oracle spec) (i : spec.ι) (s : so.S) (x : spec.domain i) :
  (so.o i s x).is_well_formed :=
so.oracle_is_well_formed i s x

def simulation_oracle.append {spec spec' : oracle_comp_spec}
  (so : simulation_oracle spec) (so' : simulation_oracle spec') :
  simulation_oracle (spec ++ spec') :=
{
  S := so.S × so'.S,
  o := λ i ss', begin
    refine i.rec_on _ _,
    refine λ i x, functor.map (prod.map id (λ s, (s, ss'.2))) (so.o i ss'.1 x),
    refine λ i x, functor.map (prod.map id (λ s', (ss'.1, s'))) (so'.o i ss'.2 x),
  end,
  oracle_is_well_formed := λ i, by induction i; apply_instance,
}


/-- Evaluation distribution of an `oracle_comp A B C` as a `comp A`.
`S` is the type of the internal state of the `A` to `B` oracle, and `s` is the initial state.
`o` takes the current oracle state and an `A` value, and computes a `B` value and new oracle state. -/
def simulate (so : simulation_oracle spec) : 
  Π {C : Type} (oc : oracle_comp spec C) (s : so.S), comp (C × so.S)
| C (oc_ret c) s := 
  (do x ← c, return (x, s))
| C (oc_bind oc od) s :=
  (do cs' ← simulate oc s,
    simulate (od cs'.fst) cs'.snd)
| C (oc_query i a) s := so.o i s a

@[simp]
lemma simulate_oc_query (so : simulation_oracle spec)
  {i : spec.ι} (a : spec.domain i) (s : so.S) :
  (oc_query i a : oracle_comp spec (spec.R i)).simulate so s = so.o i s a := 
rfl

@[simp]
lemma simulate_oc_ret (so : simulation_oracle spec)
  {C : Type} (c : comp C) (s : so.S) :
  (oc_ret c : oracle_comp spec C).simulate so s =
    c.bind (λ x, comp.ret (x, s)) :=
rfl

@[simp]
lemma simulate_oc_bind (so : simulation_oracle spec)
  {C D : Type} (oc : oracle_comp spec C) 
  (od : C → oracle_comp spec D) (s : so.S) :
  (oc_bind oc od).simulate so s = 
    (oc.simulate so s).bind (λ cs', (od cs'.1).simulate so cs'.2) :=
rfl

lemma simulate_is_well_formed (so : simulation_oracle spec)
  (oc : oracle_comp spec C) (hoc : oc.is_well_formed) (s : so.S) : 
  (oc.simulate so s).is_well_formed :=
begin
  unfreezingI { induction oc generalizing s },
  { simpa only [simulate_oc_ret, comp.bind_is_well_formed_iff, and_true, implies_true_iff, comp.ret.is_well_formed] using hoc},
  { simp only [comp.bind_is_well_formed_iff, prod.forall, simulate_oc_bind],
    refine ⟨oc_ih_oc hoc.1 s, λ c s' _, oc_ih_od c (hoc.2 c) s'⟩ },
  { simp only [simulate_oc_query],
    apply_instance },
end

@[simp]
instance simulate.is_well_formed (so : simulation_oracle spec)
  (oc : oracle_comp spec C) [hoc : oc.is_well_formed] (s : so.S) : 
  (oc.simulate so s).is_well_formed :=
simulate_is_well_formed so oc hoc s

@[derive comp.is_well_formed]
def stateless_simulate (so : simulation_oracle spec)
  (oc : oracle_comp spec C) [hoc : oc.is_well_formed] (s : so.S) :
  comp C :=
functor.map prod.fst (oc.simulate so s)

/-- Construct a simulation oracle from a stateless function,
  using internal state to log queries to the oracle -/
def logging_simulation_oracle (oc : oracle_comp spec C)
  (o : Π (i : spec.ι), spec.domain i → comp (spec.range i))
  [∀ (i : spec.ι) (x : spec.domain i), (o i x).is_well_formed] :
  simulation_oracle spec :=
{
  S := list (Σ (i : spec.ι), spec.domain i),
  o := λ t as a, (o t a >>= λ b, return (b, ⟨t, a⟩ :: as)),
  oracle_is_well_formed := by apply_instance
}

-- /-- Run the computation with a stateless oracle `o`,
--   and use the internal state to log queries -/
-- @[derive comp.is_well_formed]
-- def logging_simulate (oc : oracle_comp spec C) [oc.is_well_formed]
--   (o : Π t, spec.D t → comp (spec.R t)) [∀ t s, (o t s).is_well_formed] : comp (C × (list $ Σ (t : spec.ι), spec.D t)) :=
-- oc.simulate [] (λ t as a, (o t a >>= λ b, return (b, ⟨t, a⟩ :: as)))

-- @[simp]
-- instance logging_simulate.is_well_formed 
--   (oc : oracle_comp spec C) [hoc : oc.is_well_formed]
--   (o : Π t, spec.D t → comp (spec.R t)) [ho : ∀ t a, (o t a).is_well_formed] :
--   (logging_simulate oc o).is_well_formed :=
-- simulate_is_well_formed _ hoc _ _ (by simp)

section singleton_oracle_comp



-- def singleton_oracle_comp (A B : Type) : Type → Type 1 :=
-- oracle_comp (λ (_ : unit), A) (λ (_ : unit), B)

-- def double_oracle_comp (A B A' B' : Type) : Type → Type 1 :=
-- oracle_comp (sum.elim (λ (_ : unit), A) (λ (_ : unit), A'))
--   (sum.elim (λ _, B) (λ _, B'))

end singleton_oracle_comp

end oracle_comp