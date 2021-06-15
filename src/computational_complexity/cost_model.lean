import crypto_foundations.comp
import crypto_foundations.oracle_comp
import computational_complexity.polynomial_asymptotics
import to_mathlib

import data.real.nnreal
import analysis.special_functions.exp_log

/-!
# Cost Model for shallow embedding

This file defines a cost model for lean functions, and for instances of `comp`.
Costs are specified by an axiomatically defined proposition `has_cost f n`.
Particular proofs may need to assume additional hypotheses about `has_cost`,
  but properties of most basic functions are defined are defined here.

Since function equiality in Lean is extensional, 
  `has_cost f n → has_cost g n` whenever `f` and `g` are pointwise equal (see `has_cost_ext`).
Therefore `has_cost f n` should be thought of as saying that *some* procedure
  implementing the abstract function `f` has cost `n`,
  rather than as saying that computing `f` directly has cost `n`.

`has_cost` also only defines a lower bound on the cost (see `has_cost_of_le`),
  which is sufficient for establishing reduction in cryptographic proofs.
In particular, it suffices for establishing asymptotic behavior is polynomial / polylogarithmic.

Also note that `has_cost` assumes the input and output of functions has some *fixed* internal representation,
  and all cost statements are being made relative to this fixed representation.
This allows `has_cost` to behave well with function composition,
  but also means all axioms need to be valid in the context of shared representations.
-/

universes u v w

-- TODO: Try to get this working with some extensible system

/-- Represents a cost assignment model to Lean functions -/
def function_cost_model := ∀ {A : Type u} {B : Type v}, (A → B) → ℚ → Prop
def comp_cost_model := ∀ {A : Type}, comp A → ℚ → Prop
def oracle_comp_cost_model := ∀ {A B C : Type}, oracle_comp A B C → (ℚ → ℚ) → Prop

/-- Defines an extensible axiomatic cost model for Lean functions.
  This constant exists over arbitrary universes `u` and `v` until use, 
    in particular we allow `B` to vary over `Type` and `Type 1`. -/
constant has_cost : function_cost_model.{u v}

namespace has_cost

variables {A : Type u} {B : Type v} {C : Type w} {D : Type*}

-- Axioms for deriving costs of functions from related functions

-- TODO: Is this worth including? Maybe not useful
axiom ge_zero_of_has_cost {f : A → B} {n : ℚ} (h : has_cost f n) : n ≥ 0

/-- `has_cost` is a lower bound, so any higher cost is also a bound -/
axiom has_cost_of_le {f : A → B} {n1 n2 : ℚ} (hnm : n1 ≤ n2) :
  has_cost f n1 → has_cost f n2

/-- Context sensitive composition law, allowing both `g` and `f` to depend on the original value -/
axiom has_cost_compose {f : A → B} {g : A → B → C} {n1 n2 n3 : ℚ} :
    has_cost f n1 → has_cost g n2 → (∀ a, has_cost (g a) n3) 
      → has_cost (λ a, g a (f a)) (n1 + n2 + n3)

/-- evaluating an uncurried function is at most as expensive as evaluating the original on both inputs -/
axiom has_cost_uncurry {f : A → B → C} {n1 n2 : ℚ} :
    has_cost f n1 → (∀ a, has_cost (f a) n2) → has_cost (function.uncurry f) (n1 + n2)

/-- evaluating the original function is easier than evaluating the uncurried function -/
axiom has_cost_of_uncurry {f : A → B → C} {n : ℚ} :
    has_cost (function.uncurry f) n → has_cost f n

/-- evaluating the origianl function is easier than evaluating the uncurried function -/
axiom has_cost_of_uncurry' {f : A → B → C} {n : ℚ} (a : A) :
    has_cost (function.uncurry f) n → has_cost (f a) n

/-- componentwise evaluation is as easy as the two original evaluations -/
axiom has_cost_pair {f : A → B} {g : C → D} {n m : ℚ} :
    has_cost f n → has_cost g m → has_cost (λ (x : A × C), (f x.fst, g x.snd)) (n + m)

-- Costs of basic commonly used functions

axiom has_cost_const (b : B) :
  has_cost (λ _, b : A → B) 0

axiom has_cost_id : 
  has_cost (id : A → A) 0

axiom has_cost_fst :
    has_cost (prod.fst : A × B → A) 0

axiom has_cost_snd :
    has_cost (prod.snd : A × B → B) 0

axiom has_cost_ret {A : Type} [decidable_eq A] :
  has_cost (comp.ret : A → comp A) 0

-- Additional properties derived from the basic axioms

-- `has_cost` is extensional, so it only depends on the pointwise function behaviour
lemma has_cost_ext {f g : A → B} {n : ℚ} (hf : has_cost f n)
  (hfg : ∀ a, f a = g a) : has_cost g n :=
(funext hfg : f = g) ▸ hf 

@[simp] lemma has_cost_id_iff {n : ℚ} : 
  has_cost (id : A → A) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h has_cost_id⟩

@[simp] lemma has_cost_const_iff {b : B} {n : ℚ} :
  has_cost (λ _, b : A → B) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h (has_cost_const _)⟩

@[simp] lemma has_cost_fst_iff {n : ℚ} :
  has_cost (prod.fst : A × B → A) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h has_cost_fst⟩

@[simp] lemma has_cost_snd_iff {n : ℚ} :
  has_cost (prod.snd : A × B → B) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h has_cost_snd⟩

@[simp] lemma has_cost_ret_iff {A : Type} [decidable_eq A] {n : ℚ} :
  has_cost (comp.ret : A → comp A) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h has_cost_ret⟩

lemma has_cost_comp {f : A → B} {g : B → C} {n m : ℚ} : 
  has_cost f n → has_cost g m → has_cost (g ∘ f) (n + m) :=
λ hf hg, by simpa using has_cost_compose hf (has_cost_const _) (λ _, hg)

lemma has_cost_comp_le {f : A → B} {g : B → C} {n m p : ℚ} (h : n + m ≤ p) :
  has_cost f n → has_cost g m → has_cost (g ∘ f) p :=
λ hf hg, has_cost_of_le h (has_cost_comp hf hg)

lemma has_cost_uncurry_le {f : A → B → C} {n1 n2 n3 : ℚ} (h : n1 + n2 ≤ n3) :
  has_cost f n1 → (∀ n, has_cost (f n) n2) → has_cost (function.uncurry f) n3 :=
λ hf hg, has_cost_of_le h (has_cost_uncurry hf hg)

lemma has_cost_curry {A B C : Type} {f : (A × B) → C} {n : ℚ} :
  has_cost f n → has_cost (function.curry f) n :=
λ hf, has_cost_of_uncurry (by simpa using hf)

lemma has_cost_pair_le {f : A → B} {g : C → D} {n m p : ℚ} (h : n + m ≤ p) :
    has_cost f n → has_cost g m → has_cost (λ (x : A × C), (f x.fst, g x.snd)) (p) :=
λ hf hg, has_cost_of_le h (has_cost_pair hf hg)

end has_cost

section comp_cost
open comp

/-- Cost of a computation `comp A`, relative to a given `function_cost_model` -/
inductive comp_cost : comp_cost_model
| cost_ret {A : Type} [decidable_eq A] {a : A} :
    comp_cost (ret a) 0
| cost_bind {A B : Type} {ca : comp A} {cb : A → comp B} {n1 n2 n3 : ℚ} :
    comp_cost ca n1 → has_cost cb n2 → (∀ a, comp_cost (cb a) n3) → comp_cost (bind ca cb) (n1 + n2 + n3)
| cost_rnd_bitvec {n : ℕ} :
    comp_cost (rnd (bitvec n)) ↑n
| cost_le {A : Type} {ca : comp A} {n m : ℚ} (hnm : n ≤ m) :
    comp_cost ca n → comp_cost ca m

-- This statement holds for `has_cost` as well, but is only provable for `comp_cost`.
theorem ge_zero_of_comp_cost {A : Type} {ca : comp A} {n : ℚ} (h : comp_cost ca n) :
  n ≥ 0 :=
begin
  refine h.rec_on _ _ _ _,
  { refine λ _ _ _, le_rfl },
  { refine λ A B ca cb n1 n2 n3 _ hcb _ hn1 hn3, _,
    refine add_nonneg (add_nonneg hn1 _) (hn3 (comp_base_exists ca)),
    refine has_cost.ge_zero_of_has_cost hcb },
  { refine nat.cast_nonneg },
  { refine λ A ca n m hnm hca hn, le_trans hn hnm }
end

@[simp] lemma comp_cost_ret {A : Type} [decidable_eq A] {a : A} {n : ℚ} :
  comp_cost (ret a) n ↔ n ≥ 0 :=
⟨ge_zero_of_comp_cost, λ h, comp_cost.cost_le h comp_cost.cost_ret⟩

@[simp] lemma comp_cost_rnd_bitvec (n : ℕ) : comp_cost (rnd (bitvec n)) n :=
comp_cost.cost_rnd_bitvec

lemma comp_cost_rnd_le {n m : ℕ} (hnm : n ≤ m) : comp_cost (rnd (bitvec n)) m :=
comp_cost.cost_le (nat.cast_le.mpr hnm) comp_cost.cost_rnd_bitvec

open oracle_comp

inductive oracle_cost (fm : function_cost_model.{0 1}) (cm : comp_cost_model) : oracle_comp_cost_model
-- Querying the oracle has the same cost as the specified oracle call cost
| cost_query {A B : Type} {a : A} :
    oracle_cost (oc_query a : oracle_comp A B B) id
-- Returning the result of a `comp` has cost independent of oracle access cost
| cost_ret {A B C : Type} {c : comp C} {n : ℚ} :
    cm c n → oracle_cost (oc_ret c : oracle_comp A B C) (λ _, n)
-- TODO: This looks off
| cost_bind {A B C D : Type} {oc : oracle_comp A B C} {od : C → oracle_comp A B D} {n1 n2 n3 : ℕ} :
    oracle_cost oc n1 → fm od n2 → (∀ c, oracle_cost (od c) n3) 
      → oracle_cost (oc_bind oc od) (n1 + n2 + n3)
| cost_run {A B C A' B' S : Type} [decidable_eq A] [decidable_eq B] [decidable_eq S]
    {oc : oracle_comp A B C} {ob : S → A → oracle_comp A' B' (B × S)} {s : S} {n m : ℚ} {f g : ℚ → ℚ} :
    oracle_cost oc f → fm ob n → (∀ s, fm (ob s) m) → (∀ s a, oracle_cost (ob s a) g) 
      → oracle_cost (oc_run oc ob s) (λ n, f (n + m + (g n)))
| cost_le {A B C : Type} {oc : oracle_comp A B C} {f g : ℚ → ℚ} (hnm : ∀ n, f n ≤ g n) :
    oracle_cost oc f → oracle_cost oc g

end comp_cost