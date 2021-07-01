import crypto_foundations.comp

/-!
# Model of Nondeterministic Computation With Oracles

This file extends the `comp` monad to allow compuation with oracle access.
The definition allows for oracles to hide their internal state,
  which wouldn't be possible by just giving the adversary an explicit function.
It also allows for definitions that restrict the type of calls made to the oracle,
  e.g. an `oracle_comp M S (M × S)` attempting to forge a signature on an unqueried message.
-/

variables {A B C : Type}

/-- `oracle_comp A B C` is the type of a computation of a value of type `C`,
  with access to an oracle taking values in `A` to values in `B`.
  `oc_run` represents computing `oc` with `ob` as a proxy for the oracle
  -- Lack of impredicative `Set` type means this moves up a type universe
  TODO: the final return type can't be inferred in general without type hints -/
inductive oracle_comp : Type → Type → Type → Type 1
| oc_query {A B : Type} : Π (a : A), oracle_comp A B B
| oc_ret {A B C : Type} : Π (c : comp C), oracle_comp A B C
| oc_bind {A B C D : Type} : Π (oc : oracle_comp A B C) (od : C → oracle_comp A B D),
    oracle_comp A B D
-- | oc_run {A B C A' B' S : Type} :
--     Π (oc : oracle_comp A B C) (s : S) (ob : S → A → oracle_comp A' B' (B × S)) , 
--       oracle_comp A' B' (C × S)

@[simps]
instance oracle_comp.monad {A B : Type} : monad (oracle_comp A B) :=
{ pure := λ C c, oracle_comp.oc_ret (comp.ret c),
  bind := λ C D, oracle_comp.oc_bind }

namespace oracle_comp

/-- `oc_run` constructed manually from the other constructors -/
def oc_run : Π {A B C : Type} (oc : oracle_comp A B C) 
  {A' B' S : Type} (s : S) (o : S → A → oracle_comp A' B' (B × S)),
  oracle_comp A' B' (C × S)
| A _ B (@oc_query _ _ a) A' B' S s o := o s a
| A B C (@oc_ret _ _ _ cc) A' B' S s o := oc_ret (do c ← cc, return (c, s))
| A B D (@oc_bind _ _ C _ oc od) A' B' S s o := 
    (oc_run oc s o) >>= (λ cs, oc_run (od cs.1) cs.2 o)

/-- Every oracle_comp gives rise to a mapping from query assignments to the base comp type,
  where the value in `C` is the result of the computation if oracles behave like the input,
  and internal `comp` values return their base values
  -- TODO: rename this -/
def oracle_comp_base_exists (oc : oracle_comp A B C) : (A → B) → C :=
@oracle_comp.rec_on (λ A B C _, (A → B) → C) A B C oc
  (λ A B a q, q a) (λ A B C cc hcc, cc.comp_base_exists)
  (λ A B C D oc od hoc hod q, hod (hoc q) q)

section is_well_formed

@[class]
def is_well_formed : Π {A B C : Type}, oracle_comp A B C → Prop
| A B _ (oc_query a) := true
| A B C (oc_ret cc) := cc.is_well_formed
| A B D (@oc_bind _ _ C _ oc od) := oc.is_well_formed ∧ ∀ c, (od c).is_well_formed

@[simp]
lemma oc_query_is_well_formed {A : Type} (a : A) (B : Type) :
  (oc_query a : oracle_comp A B B).is_well_formed :=
by simp [is_well_formed]

@[simp]
lemma oc_ret_is_well_formed_iff {A B C : Type} (c : comp C) :
  (oc_ret c : oracle_comp A B C).is_well_formed ↔ c.is_well_formed :=
iff.rfl

@[simp]
lemma oc_bind_is_well_formed_iff {A B C D : Type} 
  (oc : oracle_comp A B C) (od : C → oracle_comp A B D) :
  (oc_bind oc od).is_well_formed ↔
    oc.is_well_formed ∧ ∀ c, (od c).is_well_formed :=
iff.rfl

@[simp]
instance oc_query.is_well_formed {A B : Type} (a : A) :
  (oc_query a : oracle_comp A B B).is_well_formed :=
by simp

@[simp]
instance oc_ret.is_well_formed {A B C : Type} (cc : comp C) [h : cc.is_well_formed] :
  (oc_ret cc : oracle_comp A B C).is_well_formed :=
by simp [h]

@[simp]
instance oc_bind.is_well_formed {A B C D : Type} (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
  [hoc : is_well_formed oc] [hod : ∀ c, is_well_formed $ od c] :
  (oc_bind oc od).is_well_formed :=
by simp [hoc, hod]

lemma is_well_formed_of_oc_bind_left {A B C D : Type}
  {oc : oracle_comp A B C} {od : C → oracle_comp A B D} : 
  (oc >>= od).is_well_formed → oc.is_well_formed :=
λ h, h.1

lemma is_well_formed_of_oc_bind_right {A B C D : Type}
  {oc : oracle_comp A B C} {od : C → oracle_comp A B D} :
  (oc >>= od).is_well_formed → ∀ c, (od c).is_well_formed :=
λ h, h.2

end is_well_formed

/-- Evaluation distribution of an `oracle_comp A B C` as a `comp A`.
`S` is the type of the internal state of the `A` to `B` oracle, and `s` is the initial state.
`o` takes the current oracle state and an `A` value, and computes a `B` value and new oracle state. -/
def eval_distribution (oc : oracle_comp A B C) :
  Π {S : Type} (s : S) (o : S → A → comp (B × S)), comp (C × S) :=
begin
  induction oc with A B a A B C c A B C D oc od hoc hod A B C A' B' S' oc s' ob hoc hob,
  { exact λ S s o, o s a },
  { exact λ S s o,
      c.bind (λ x, @comp.ret (C × S) (x, s)) },
  { exact λ S s o, (@hoc S s o).bind (λ cs', @hod cs'.fst S cs'.snd o) },
end

@[simp]
lemma eval_distribution_oc_query {A B S : Type}
  (a : A) (s : S) (o : S → A → comp (B × S)) :
  (oc_query a : oracle_comp A B B).eval_distribution s o = o s a := 
rfl

@[simp]
lemma eval_distribution_oc_ret {A B C S : Type}
  (c : comp C) (s : S) (o : S → A → comp (B × S)) :
  (oc_ret c : oracle_comp A B C).eval_distribution s o =
    c.bind (λ x, @comp.ret (C × S) (x, s)) :=
rfl 

@[simp]
lemma eval_distribution_oc_bind {A B C D S : Type}
  (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
  (s : S) (o : S → A → comp (B × S)) :
  (oc_bind oc od).eval_distribution s o = 
    (oc.eval_distribution s o).bind (λ cs', (od cs'.1).eval_distribution cs'.2 o) :=
rfl

lemma eval_distribution_is_well_formed {S : Type} 
  (oc : oracle_comp A B C) (hoc : oc.is_well_formed)
  (s : S) (o : S → A → comp (B × S)) (ho : ∀ s a, (o s a).is_well_formed) : 
  (eval_distribution oc s o).is_well_formed :=
begin
  unfreezingI { induction oc generalizing s },
  { simp only [ho, eval_distribution_oc_query]},
  { simpa only [eval_distribution_oc_ret, comp.bind_is_well_formed_iff, and_true, implies_true_iff, comp.ret.is_well_formed] using hoc},
  { simp only [comp.bind_is_well_formed_iff, prod.forall, eval_distribution_oc_bind],
    refine ⟨oc_ih_oc hoc.1 o ho s, λ c s' _, oc_ih_od c (hoc.2 c) o ho s'⟩ },
end

@[simp]
instance eval_distribution.is_well_formed {S : Type} 
  (oc : oracle_comp A B C) [hoc : oc.is_well_formed] 
  (s : S) (o : S → A → comp (B × S)) [ho : ∀ s a, (o s a).is_well_formed] :
  (oc.eval_distribution s o).is_well_formed :=
eval_distribution_is_well_formed oc hoc s o ho

/-- Run the computation using internal state to track queries -/
def logging_eval_distribution (oc : oracle_comp A B C)
  (o : A → comp B) : comp (C × (list A)) :=
begin
  refine (oc.eval_distribution [] (λ as a, _)),
  refine (o a >>= λ b, return (b, a :: as)),
end

lemma logging_eval_distribution_is_well_formed
  (oc : oracle_comp A B C) (hoc : oc.is_well_formed)
  (o : A → comp B) (ho : ∀ a, (o a).is_well_formed) :
  (logging_eval_distribution oc o).is_well_formed :=
by unfold logging_eval_distribution; apply_instance

@[simp]
instance logging_eval_distribution.is_well_formed 
  (oc : oracle_comp A B C) [hoc : oc.is_well_formed]
  (o : A → comp B) [ho : ∀ a, (o a).is_well_formed] :
  (logging_eval_distribution oc o).is_well_formed :=
logging_eval_distribution_is_well_formed oc hoc o ho
  
/-- Evaluation distribution for a stateless oracle with `f` simulating the oracle. -/
def stateless_eval_distribution (oc : oracle_comp A B C) 
  (o : A → comp B) : comp C :=
(logging_eval_distribution oc o) >>= (λ cas, comp.ret cas.1)

lemma stateless_eval_distribution_is_well_formed
  (oc : oracle_comp A B C) (hoc : oc.is_well_formed)
  (o : A → comp B) (ho : ∀ a, (o a).is_well_formed) :
  (oc.stateless_eval_distribution o).is_well_formed :=
by unfold stateless_eval_distribution; apply_instance

@[simp]
instance stateless_eval_distribution.is_well_formed
  (oc : oracle_comp A B C) [hoc : oc.is_well_formed]
  (o : A → comp B) [ho : ∀ a, (o a).is_well_formed] :
  (oc.stateless_eval_distribution o).is_well_formed :=
stateless_eval_distribution_is_well_formed oc hoc o ho

end oracle_comp