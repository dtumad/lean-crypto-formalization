import comp
import polynomial_asymptotics
import to_mathlib
import data.real.nnreal
import analysis.special_functions.exp_log

/-!
# Cost Model for shallow embedding

This file defines a cost model for lean functions, and for instances of `Comp`.
Costs are specified by an axiomatically defined proposition `has_cost f n`.
Particular proofs may need to assume additional hypotheses about `has_cost`,
  but properties of most basic functions are defined are defined here.

Since functions equiality in Lean is extensional, 
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
def function_cost_model := ∀ {A : Type u} {B : Type v}, (A → B) → ℚ → Prop
def comp_cost_model := ∀ {A : Type}, Comp A → ℚ → Prop
def oracle_comp_cost_model := ∀ {A B C : Type}, Comp.Oracle_Comp A B C → (ℚ → ℚ) → Prop

/-- Defines an extensible axiomatic cost model for Lean functions.
  This constant exists over arbitrary universes `u` and `v` until use,
    in particular we allow `B` to vary over `Type` and `Type 1`. -/
constant has_cost : function_cost_model.{u v}

namespace has_cost

variables {A : Type u} {B : Type v} {C : Type w}

/-- Axioms for deriving costs of functions from related functions -/
axiom ge_zero_of_has_cost {f : A → B} {n : ℚ} (h : has_cost f n) : n ≥ 0

axiom has_cost_of_le {f : A → B} {n m : ℚ} (hnm : n ≤ m) :
  has_cost f n → has_cost f m

axiom has_cost_compose {f : A → B} {g : A → B → C} {n1 n2 n3 : ℚ} :
    has_cost f n1 → has_cost g n2 → (∀ a, has_cost (g a) n3) 
      → has_cost (λ a, g a (f a)) (n1 + n2 + n3)

axiom has_cost_uncurry {f : A → B → C} {n1 n2 : ℚ} :
    has_cost f n1 → (∀ a, has_cost (f a) n2) → has_cost (function.uncurry f) (n1 + n2)

axiom has_cost_of_uncurry {f : A → B → C} {n : ℚ} :
    has_cost (function.uncurry f) n → has_cost f n

axiom has_cost_of_uncurry' {f : A → B → C} {n : ℚ} (a : A) :
    has_cost (function.uncurry f) n → has_cost (f a) n

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
  has_cost (Comp.ret : A → Comp A) 0

/-- Additional properties derived from the basic axioms -/

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

end has_cost

section comp_cost
open Comp

/-- Cost of a computation `Comp A`, relative to a given `function_cost_model` -/
inductive comp_cost (fm : function_cost_model.{0 1}) : comp_cost_model
| cost_ret {A : Type} [decidable_eq A] {a : A} :
    comp_cost (ret a) 0
| cost_bind {A B : Type} {ca : Comp A} {cb : A → Comp B} {n1 n2 n3 : ℕ} :
    comp_cost ca n1 → fm cb n2 → (∀ a, comp_cost (cb a) n3) → comp_cost (bind ca cb) (n1 + n2 + n3)
| cost_rnd_bitvec {n : ℕ} :
    comp_cost (rnd (bitvec n)) n
| cost_le {A : Type} {ca : Comp A} {n m : ℕ} (hnm : n ≤ m) :
    comp_cost ca n → comp_cost ca m

variables {fm : function_cost_model.{0 1}}

@[simp] lemma comp_cost_ret {A : Type} [decidable_eq A] {a : A} {n : ℕ} :
  comp_cost @fm (ret a) n :=
comp_cost.cost_le (zero_le n) comp_cost.cost_ret

@[simp] lemma comp_cost_rnd_bitvec (n : ℕ) : comp_cost @fm (rnd (bitvec n)) n :=
comp_cost.cost_rnd_bitvec

lemma comp_cost_rnd_le {n m : ℕ} (hnm : n ≤ m) : comp_cost @fm (rnd (bitvec n)) m :=
comp_cost.cost_le hnm comp_cost.cost_rnd_bitvec

open Comp.Oracle_Comp

inductive oracle_cost (fm : function_cost_model.{0 1}) (cm : comp_cost_model) : oracle_comp_cost_model
| cost_query {A B : Type} {a : A} :
    oracle_cost (oc_query a : Oracle_Comp A B B) id
| cost_ret {A B C : Type} {c : Comp C} {n : ℕ} :
    cm c n → oracle_cost (oc_ret c : Oracle_Comp A B C) n
| cost_bind {A B C D : Type} {oc : Oracle_Comp A B C} {od : C → Oracle_Comp A B D} {n1 n2 n3 : ℕ} :
    oracle_cost oc n1 → fm od n2 → (∀ c, oracle_cost (od c) n3) 
      → oracle_cost (oc_bind oc od) (n1 + n2 + n3)
| cost_run {A B C A' B' S : Type} [decidable_eq A] [decidable_eq B] [decidable_eq S]
    {oc : Oracle_Comp A B C} {ob : S → A → Oracle_Comp A' B' (B × S)} {s : S} {n m : ℕ} {f g : ℚ → ℚ} :
    oracle_cost oc f → fm ob n → (∀ s, fm (ob s) m) → (∀ s a, oracle_cost (ob s a) g) 
      → oracle_cost (oc_run oc ob s) (λ n, f (n + m + (g n)))
| cost_le {A B C : Type} {oc : Oracle_Comp A B C} {n m : ℕ} (hnm : n ≤ m) :
    oracle_cost oc n → oracle_cost oc m

end comp_cost

section poly_time_Comp

def poly_time_cost {A B : ℕ → Type} (c : Π n, A n → B n) :=
  ∃ (f : ℚ → ℚ), poly_growth f ∧ (∀ n, has_cost (c n) (f n))

theorem poly_time_cost_ext {A B : ℕ → Type} {c c' : Π n, A n → B n}
  (hc : poly_time_cost c) (h : ∀ n a, c n a = c' n a) :
  poly_time_cost c' :=
(funext (λ n, funext (λ a, h n a)) : c = c') ▸ hc

def poly_time_Comp {A : ℕ → Type} (c : Π n, Comp (A n)) :=
  ∃ (f : ℚ → ℚ), poly_growth f ∧ (∀ n, comp_cost @has_cost (c n) (f n))

end poly_time_Comp