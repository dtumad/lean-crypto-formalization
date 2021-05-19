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
-/

open_locale nnreal

universes u v w



-- TODO: look more closely at explicit vs. implicit parameters

/-- Represents a cost assignment model to Lean functions -/
def function_cost_model := ∀ {A : Type u} {B : Type v}, (A → B) → ℝ → Prop
def comp_cost_model := ∀ {A : Type}, comp A → ℝ → Prop
def oracle_comp_cost_model := ∀ {A B C : Type}, oracle_comp A B C → (ℝ → ℝ) → Prop

/-- Defines an extensible axiomatic cost model for Lean functions.
  This constant exists over arbitrary universes `u` and `v` until use,
    in particular we allow `B` to vary over `Type` and `Type 1`. -/
constant has_cost : function_cost_model.{u v}

namespace has_cost

variables {A : Type u} {B : Type v} {C : Type w} {D : Type*}

/-- Axioms for deriving costs of functions from related functions -/
axiom ge_zero_of_has_cost {f : A → B} {n : ℝ} (h : has_cost f n) : n ≥ 0

axiom has_cost_of_le {f : A → B} {n m : ℝ} (hnm : n ≤ m) :
  has_cost f n → has_cost f m

axiom has_cost_compose {f : A → B} {g : A → B → C} {n1 n2 n3 : ℝ} :
    has_cost f n1 → has_cost g n2 → (∀ a, has_cost (g a) n3) 
      → has_cost (λ a, g a (f a)) (n1 + n2 + n3)

axiom has_cost_uncurry {f : A → B → C} {n1 n2 : ℝ} :
    has_cost f n1 → (∀ a, has_cost (f a) n2) → has_cost (function.uncurry f) (n1 + n2)

axiom has_cost_of_uncurry {f : A → B → C} {n : ℝ} :
    has_cost (function.uncurry f) n → has_cost f n

axiom has_cost_of_uncurry' {f : A → B → C} {n : ℝ} (a : A) :
    has_cost (function.uncurry f) n → has_cost (f a) n

axiom has_cost_pair {f : A → B} {g : C → D} {n m : ℝ} :
    has_cost f n → has_cost g m → has_cost (λ (x : A × C), (f x.fst, g x.snd)) (n + m)

/-- Costs of basic commonly used functions -/
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

/-- Additional properties derived from the basic axioms -/

lemma has_cost_ext {f g : A → B} {n : ℝ} (hf : has_cost f n)
  (hfg : ∀ a, f a = g a) : has_cost g n :=
(funext hfg : f = g) ▸ hf 

@[simp] lemma has_cost_id_iff {n : ℝ} : 
  has_cost (id : A → A) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h has_cost_id⟩

@[simp] lemma has_cost_const_iff {b : B} {n : ℝ} :
  has_cost (λ _, b : A → B) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h (has_cost_const _)⟩

@[simp] lemma has_cost_fst_iff {n : ℝ} :
  has_cost (prod.fst : A × B → A) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h has_cost_fst⟩

@[simp] lemma has_cost_snd_iff {n : ℝ} :
  has_cost (prod.snd : A × B → B) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h has_cost_snd⟩

@[simp] lemma has_cost_ret_iff {A : Type} [decidable_eq A] {n : ℝ} :
  has_cost (comp.ret : A → comp A) n ↔ n ≥ 0 :=
⟨ge_zero_of_has_cost, λ h, has_cost_of_le h has_cost_ret⟩

lemma has_cost_comp {f : A → B} {g : B → C} {n m : ℝ} : 
  has_cost f n → has_cost g m → has_cost (g ∘ f) (n + m) :=
λ hf hg, by simpa using has_cost_compose hf (has_cost_const _) (λ _, hg)

lemma has_cost_comp_le {f : A → B} {g : B → C} {n m p : ℝ} (h : n + m ≤ p) :
  has_cost f n → has_cost g m → has_cost (g ∘ f) p :=
λ hf hg, has_cost_of_le h (has_cost_comp hf hg)

lemma has_cost_uncurry_le {f : A → B → C} {n1 n2 n3 : ℝ} (h : n1 + n2 ≤ n3) :
  has_cost f n1 → (∀ n, has_cost (f n) n2) → has_cost (function.uncurry f) n3 :=
λ hf hg, has_cost_of_le h (has_cost_uncurry hf hg)

lemma has_cost_curry {A B C : Type} {f : (A × B) → C} {n : ℝ} :
  has_cost f n → has_cost (function.curry f) n :=
λ hf, has_cost_of_uncurry (by simpa using hf)

lemma has_cost_pair_le {f : A → B} {g : C → D} {n m p : ℝ} (h : n + m ≤ p) :
    has_cost f n → has_cost g m → has_cost (λ (x : A × C), (f x.fst, g x.snd)) (p) :=
λ hf hg, has_cost_of_le h (has_cost_pair hf hg)

end has_cost

section comp_cost
open comp

/-- Cost of a computation `comp A`, relative to a given `function_cost_model` -/
inductive comp_cost : comp_cost_model
| cost_ret {A : Type} [decidable_eq A] {a : A} :
    comp_cost (ret a) 0
| cost_bind {A B : Type} {ca : comp A} {cb : A → comp B} {n1 n2 n3 : ℕ} :
    comp_cost ca n1 → has_cost cb n2 → (∀ a, comp_cost (cb a) n3) → comp_cost (bind ca cb) (n1 + n2 + n3)
| cost_rnd_bitvec {n : ℕ} :
    comp_cost (rnd (bitvec n)) ↑n
| cost_le {A : Type} {ca : comp A} {n m : ℝ} (hnm : n ≤ m) :
    comp_cost ca n → comp_cost ca m

theorem ge_zero_of_comp_cost {A : Type} {ca : comp A} {n : ℝ} (h : comp_cost ca n) :
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

@[simp] lemma comp_cost_ret {A : Type} [decidable_eq A] {a : A} {n : ℝ} :
  comp_cost (ret a) n ↔ n ≥ 0 :=
⟨ge_zero_of_comp_cost, λ h, comp_cost.cost_le h comp_cost.cost_ret⟩

@[simp] lemma comp_cost_rnd_bitvec (n : ℕ) : comp_cost (rnd (bitvec n)) n :=
comp_cost.cost_rnd_bitvec

lemma comp_cost_rnd_le {n m : ℕ} (hnm : n ≤ m) : comp_cost (rnd (bitvec n)) m :=
comp_cost.cost_le (nat.cast_le.mpr hnm) comp_cost.cost_rnd_bitvec

open oracle_comp

inductive oracle_cost (fm : function_cost_model.{0 1}) (cm : comp_cost_model) : oracle_comp_cost_model
| cost_query {A B : Type} {a : A} :
    oracle_cost (oc_query a : oracle_comp A B B) id
| cost_ret {A B C : Type} {c : comp C} {n : ℕ} :
    cm c n → oracle_cost (oc_ret c : oracle_comp A B C) n
| cost_bind {A B C D : Type} {oc : oracle_comp A B C} {od : C → oracle_comp A B D} {n1 n2 n3 : ℕ} :
    oracle_cost oc n1 → fm od n2 → (∀ c, oracle_cost (od c) n3) 
      → oracle_cost (oc_bind oc od) (n1 + n2 + n3)
| cost_run {A B C A' B' S : Type} [decidable_eq A] [decidable_eq B] [decidable_eq S]
    {oc : oracle_comp A B C} {ob : S → A → oracle_comp A' B' (B × S)} {s : S} {n m : ℕ} {f g : ℝ → ℝ} :
    oracle_cost oc f → fm ob n → (∀ s, fm (ob s) m) → (∀ s a, oracle_cost (ob s a) g) 
      → oracle_cost (oc_run oc ob s) (λ n, f (n + m + (g n)))
| cost_le {A B C : Type} {oc : oracle_comp A B C} {n m : ℕ} (hnm : n ≤ m) :
    oracle_cost oc n → oracle_cost oc m

end comp_cost