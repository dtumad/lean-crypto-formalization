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
inductive is_well_formed : ∀ {A B C : Type}, oracle_comp A B C → Prop
| well_formed_oc_query {A B : Type} (a : A) : 
    is_well_formed (oc_query a : oracle_comp A B B)
| well_formed_oc_ret {A B C : Type} (c : comp C) (hc : c.is_well_formed) :
    is_well_formed (oc_ret c : oracle_comp A B C)
| well_formed_oc_bind {A B C D : Type} (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
    (hoc : is_well_formed oc) (hod : ∀ c, is_well_formed $ od c) :
    is_well_formed (oc_bind oc od)

@[simp]
instance oc_query.is_well_formed {A B : Type} (a : A) :
  (oc_query a : oracle_comp A B B).is_well_formed :=
is_well_formed.well_formed_oc_query a

@[simp]
instance oc_ret.is_well_formed {A B C : Type} (c : comp C) [hc : c.is_well_formed] :
  (oc_ret c : oracle_comp A B C).is_well_formed :=
is_well_formed.well_formed_oc_ret c hc

@[simp]
instance oc_bind.is_well_formed {A B C D : Type} (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
  [hoc : is_well_formed oc] [hod : ∀ c, is_well_formed $ od c] :
  (oc_bind oc od).is_well_formed :=
is_well_formed.well_formed_oc_bind oc od hoc hod

-- @[elab_as_eliminator]
theorem is_well_formed_induction (p : ∀ (A B C : Type) (oc : oracle_comp A B C), Prop)
  (h_query : ∀ {A B : Type} (a : A), 
    p A B B (oc_query a))
  (h_ret : ∀ {A B C : Type} (cc : comp C) (hcc : cc.is_well_formed), 
    p A B C (oc_ret cc))
  (h_bind : ∀ {A B C D : Type} (oc : oracle_comp A B C) (od : C → oracle_comp A B D)
    (hoc : oc.is_well_formed) (hod : ∀ c, (od c).is_well_formed)
    (h : p A B C oc) (h' : ∀ c, p A B D (od c)),
    p A B D (oc_bind oc od)) :
  Π {A B C : Type} (oc : oracle_comp A B C) [hoc : oc.is_well_formed], p A B C oc
| A B C _ (is_well_formed.well_formed_oc_query a) := h_query a
| A B C _ (is_well_formed.well_formed_oc_ret cc hcc) := h_ret cc hcc 
| A B C _ (is_well_formed.well_formed_oc_bind oc od hoc hod) := h_bind oc od hoc hod (
   @is_well_formed_induction A B _ oc hoc) begin
   exact λ c, @is_well_formed_induction A B C (od c) (hod c),
   end

@[simp]
lemma oc_ret_is_well_formed_iff {A B C : Type} (c : comp C) :
  (oc_ret c : oracle_comp A B C).is_well_formed ↔ c.is_well_formed :=
begin
  refine ⟨λ h, _, λ h, is_well_formed.well_formed_oc_ret c h⟩,
  cases h,
  exact h_hc,
end

lemma is_well_formed_of_oc_bind_left {A B C D : Type}
  {oc : oracle_comp A B C} {od : C → oracle_comp A B D} : 
  (oc >>= od).is_well_formed → oc.is_well_formed
| (is_well_formed.well_formed_oc_bind oc od h h') := h

lemma is_well_formed_of_oc_bind_right {A B C D : Type}
  {oc : oracle_comp A B C} {od : C → oracle_comp A B D} :
  (oc >>= od).is_well_formed → ∀ c, (od c).is_well_formed
| (is_well_formed.well_formed_oc_bind oc od h h') := h'

@[simp]
lemma oc_bind_is_well_formed_iff {A B C D : Type} 
  (oc : oracle_comp A B C) (od : C → oracle_comp A B D) :
  (oc >>= od).is_well_formed ↔ 
    oc.is_well_formed ∧ ∀ c, (od c).is_well_formed :=
⟨λ h, ⟨is_well_formed_of_oc_bind_left h, is_well_formed_of_oc_bind_right h⟩,
  λ h, is_well_formed.well_formed_oc_bind oc od h.1 h.2⟩

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

instance eval_distribution.is_well_formed (oc : oracle_comp A B C) [oc.is_well_formed] 
 : ∀ {S : Type} (s : S) (o : S → A → comp (B × S)) (ho : ∀ s a, (o s a).is_well_formed), 
  (oc.eval_distribution s o).is_well_formed 
  :=
begin
  refine (is_well_formed_induction 
    (λ A B C oc, ∀ (S : Type) (s : S) (o : S → A → comp (B × S)) (ho : ∀ s a, (o s a).is_well_formed), 
  (oc.eval_distribution s o).is_well_formed) _ _ _ oc),
  { intros A B a S s o ho,
    simpa using ho s a },
  { intros A B C cc S s o ho h,
    simpa },
  { introsI A B C D oc od hoc hod h h' S s o ho,
    simp at ⊢ h',
    refine ⟨h S s o ho, λ c s _, h' c S s _ _⟩,
    refine ho },
end

/-- Run the computation using internal state to track queries -/
def logging_eval_distribution (oc : oracle_comp A B C)
  (o : A → comp B) : comp (C × (list A)) :=
begin
  refine (oc.eval_distribution [] (λ as a, _)),
  refine (o a >>= λ b, return (b, a :: as)),
end

@[simp]
instance logging_eval_distribution.is_well_formed 
  (oc : oracle_comp A B C) (hoc : oc.is_well_formed)
  (o : A → comp B) (ho : ∀ a, (o a).is_well_formed) :
  (logging_eval_distribution oc o).is_well_formed :=
begin
  simp [logging_eval_distribution],
  refine eval_distribution.is_well_formed oc [] _ _,
  simpa using ho,
end
  
/-- Evaluation distribution for a stateless oracle with `f` simulating the oracle. -/
def stateless_eval_distribution
  (oc : oracle_comp A B C) (f : A → comp B) : comp C :=
(logging_eval_distribution oc f) >>= (λ cas, comp.ret cas.1)

@[simp]
instance stateless_eval_distribution.is_well_formed
  (oc : oracle_comp A B C) (hoc : oc.is_well_formed)
  (o : A → comp B) (ho : ∀ a, (o a).is_well_formed) :
  (oc.stateless_eval_distribution o).is_well_formed :=
begin
  simp [stateless_eval_distribution],
  exact logging_eval_distribution.is_well_formed oc hoc o ho,
end

end oracle_comp