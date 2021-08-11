import crypto_foundations.computational_monads.comp

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

def oracle_comp_spec.domain (spec : oracle_comp_spec)
  (i : spec.ι) : Type :=
spec.D i

def oracle_comp_spec.range (spec : oracle_comp_spec)
  (i : spec.ι) : Type :=
spec.R i

/-- `oracle_comp A B C` is the type of a computation of a value of type `C`,
  with access to a family of oracle taking values in `A t` to values in `B t`.
  The oracle's semantics aren't specified until evaluation (`eval_distribution`),
    since algorithm specification only needs to know the types, not the values.
    
  The type `T` is used to index multiple oracles,
    e.g. taking `T := fin 2` gives access to two distinct oracles -/
inductive oracle_comp (spec : oracle_comp_spec) : Type → Type 1
| oc_ret {C : Type} (c : comp C) : oracle_comp C
| oc_bind {C D : Type} (oc : oracle_comp C) (od : C → oracle_comp D) : oracle_comp D
| oc_query {i : spec.ι} (a : spec.domain i) : oracle_comp (spec.range i)

instance oracle_comp.monad (spec : oracle_comp_spec) : monad (oracle_comp A B) :=
{ pure := λ C c, oracle_comp.oc_ret (comp.ret c), 
  bind := λ C D oc od, oc.oc_bind od }

variables 

namespace oracle_comp

variables {T : Type} {A B : T → Type} {C : Type}

/-- Simulate an `A → B` oracle as an `A' → B'` oracle,
  using the stateful function `o` with initial state `s` -/
def oc_run {T T' S : Type} {A B : T → Type} {A' B' : T → Type} :
  Π {C : Type} (oc : oracle_comp A B C) (s : S)
    (o : Π t, S → A t → oracle_comp A' B' (B t × S)),
  oracle_comp A' B' (C × S)
| _ (oc_query a) s o := o _ s a
| _ (oc_ret cc) s o := oc_ret (cc >>= λ c, return (c, s))
| _ (oc_bind oc od) s o := (oc_run oc s o) >>= (λ cs, oc_run (od cs.1) cs.2 o)

/-- Every oracle_comp gives rise to a mapping from query assignments to the base comp type,
  where the value in `C` is the result of the computation if oracles behave like the input,
  and internal `comp` values return their base values -/
def oracle_comp_base_exists (oc : oracle_comp A B C) : (Π t, A t → B t) → C :=
oracle_comp.rec_on oc (λ C c _, comp.comp_base_exists c) 
  (λ C D oc od hoc hod o, hod (hoc o) o) (λ t a o, o t a)

section is_well_formed

@[class]
def is_well_formed : Π {C : Type}, oracle_comp A B C → Prop
| _ (oc_query a) := true
| _ (oc_ret cc) := cc.is_well_formed
| _ (oc_bind oc od) := oc.is_well_formed ∧ ∀ c, (od c).is_well_formed

@[simp]
lemma oc_query_is_well_formed {t : T} (a : A t) :
  (oc_query a : oracle_comp A B (B t)).is_well_formed :=
true.intro

@[simp]
lemma oc_ret_is_well_formed_iff {C : Type} (c : comp C) :
  (oc_ret c : oracle_comp A B C).is_well_formed ↔ c.is_well_formed :=
iff.rfl

@[simp]
lemma oc_bind_is_well_formed_iff {C D : Type} 
  (oc : oracle_comp A B C) (od : C → oracle_comp A B D) :
  (oc_bind oc od).is_well_formed ↔
    oc.is_well_formed ∧ ∀ c, (od c).is_well_formed :=
iff.rfl

@[simp]
instance oc_query.is_well_formed {t : T} (a : A t) :
  (oc_query a : oracle_comp A B (B t)).is_well_formed :=
by simp

@[simp]
instance oc_ret.is_well_formed {C : Type} (cc : comp C) 
  [h : cc.is_well_formed] : (oc_ret cc : oracle_comp A B C).is_well_formed :=
by simp [h]

@[simp]
instance oc_bind.is_well_formed {C D : Type} (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
  [hoc : is_well_formed oc] [hod : ∀ c, is_well_formed $ od c] :
  (oc_bind oc od).is_well_formed :=
by simp [hoc, hod]

lemma is_well_formed_of_oc_bind_left {C D : Type}
  {oc : oracle_comp A B C} {od : C → oracle_comp A B D} : 
  (oc >>= od).is_well_formed → oc.is_well_formed :=
λ h, h.1

lemma is_well_formed_of_oc_bind_right {C D : Type}
  {oc : oracle_comp A B C} {od : C → oracle_comp A B D} :
  (oc >>= od).is_well_formed → ∀ c, (od c).is_well_formed :=
λ h, h.2

end is_well_formed

/-- Evaluation distribution of an `oracle_comp A B C` as a `comp A`.
`S` is the type of the internal state of the `A` to `B` oracle, and `s` is the initial state.
`o` takes the current oracle state and an `A` value, and computes a `B` value and new oracle state. -/
def simulate : Π {C : Type} (oc : oracle_comp A B C) 
  {S : Type} (s : S) (o : Π t, S → A t → comp (B t × S)), comp (C × S)
| C (oc_ret c) S s o := 
  (do x ← c, return (x, s))
| C (oc_bind oc od) S s o :=
  (do cs' ← simulate oc s o,
    simulate (od cs'.fst) cs'.snd o)
| C (oc_query a) S s o := o _ s a

@[simp]
lemma simulate_oc_query {t : T} {S : Type}
  (a : A t) (s : S) (o : Π t, S → A t → comp (B t × S)) :
  (oc_query a : oracle_comp A B (B t)).simulate s o = o t s a := 
rfl

@[simp]
lemma simulate_oc_ret {C S : Type}
  (c : comp C) (s : S) (o : Π t, S → A t → comp (B t × S)) :
  (oc_ret c : oracle_comp A B C).simulate s o =
    c.bind (λ x, @comp.ret (C × S) (x, s)) :=
rfl 

@[simp]
lemma simulate_oc_bind {C D S : Type}
  (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
  (s : S) (o : Π t, S → A t → comp (B t × S)) :
  (oc_bind oc od).simulate s o = 
    (oc.simulate s o).bind (λ cs', (od cs'.1).simulate cs'.2 o) :=
rfl

lemma simulate_is_well_formed {S : Type} 
  (oc : oracle_comp A B C) (hoc : oc.is_well_formed)
  (s : S) (o : Π t, S → A t → comp (B t × S)) (ho : ∀ t s a, (o t s a).is_well_formed) : 
  (simulate oc s o).is_well_formed :=
begin
  unfreezingI { induction oc generalizing s },
  { simpa only [simulate_oc_ret, comp.bind_is_well_formed_iff, and_true, implies_true_iff, comp.ret.is_well_formed] using hoc},
  { simp only [comp.bind_is_well_formed_iff, prod.forall, simulate_oc_bind],
    refine ⟨oc_ih_oc hoc.1 s, λ c s' _, oc_ih_od c (hoc.2 c) s'⟩ },
  { simp only [ho, simulate_oc_query]},

end

@[simp]
instance simulate.is_well_formed {S : Type} 
  (oc : oracle_comp A B C) [hoc : oc.is_well_formed] 
  (s : S) (o : Π t, S → A t → comp (B t × S)) [ho : ∀ t s a, (o t s a).is_well_formed] :
  (oc.simulate s o).is_well_formed :=
simulate_is_well_formed oc hoc s o ho

/-- Run the computation with a stateless oracle `o`,
  and use the internal state to log queries -/
def logging_simulate (oc : oracle_comp A B C)
  (o : Π t, A t → comp (B t)) : comp (C × (list $ Σ (t : T), A t)) :=
oc.simulate [] (λ t as a, (o t a >>= λ b, return (b, ⟨t, a⟩ :: as)))

@[simp]
instance logging_simulate.is_well_formed 
  (oc : oracle_comp A B C) [hoc : oc.is_well_formed]
  (o : Π t, A t → comp (B t)) [ho : ∀ t a, (o t a).is_well_formed] :
  (logging_simulate oc o).is_well_formed :=
simulate_is_well_formed _ hoc _ _ (by simp)

section singleton_oracle_comp

def singleton_oracle_comp (A B : Type) : Type → Type 1 :=
oracle_comp (λ (_ : unit), A) (λ (_ : unit), B)

def double_oracle_comp (A B A' B' : Type) : Type → Type 1 :=
oracle_comp (sum.elim (λ (_ : unit), A) (λ (_ : unit), A'))
  (sum.elim (λ _, B) (λ _, B'))

end singleton_oracle_comp

end oracle_comp