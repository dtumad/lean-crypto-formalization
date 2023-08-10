/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import computational_monads.oracle_spec

/-!
# Lists Indexed by Oracles

This file defines a `indexed_list` structure for tracking information about queries to oracles,
keeping a list of values for each of the oracles in a given `oracle_spec`.
The structure also contains a finite set `active_oracles` of indices with non-empty tracking sets,
ensuring that only finitely many oracles are actively being tracked at once.

This is used to define a number of other types, all as specific instances:
* `query_seed` tracks pre-computed seed values for results of oracle queries.
* `query_count` tracks the number of queries made to during computation.
* `query_log` tracks the input and output values of queries to each of the oracles.
-/

namespace oracle_spec

variables {α β γ : Type} {spec : oracle_spec}

@[ext] structure indexed_list (spec : oracle_spec) (τ : spec.ι → Type) :=
(to_fun (i : spec.ι) : list (τ i))
(active_oracles : finset spec.ι)
(mem_active_oracles_iff' (i : spec.ι) : i ∈ active_oracles ↔ to_fun i ≠ [])

variables {τ τ' : spec.ι → Type}

/-- View an `indexed_list` as a function from oracle index to a list of values. -/
instance indexed_list.fun_like : fun_like (indexed_list spec τ) spec.ι (λ i, list (τ i)) :=
{ coe := indexed_list.to_fun,
  coe_injective' := λ qs qs' h, indexed_list.ext qs qs' h (finset.ext (λ i,
    by rw [qs.mem_active_oracles_iff', qs'.mem_active_oracles_iff', h])) }

namespace indexed_list

section empty

def empty (spec : oracle_spec) (τ : spec.ι → Type) : indexed_list spec τ :=
{ to_fun := λ i, [],
  active_oracles := ∅,
  mem_active_oracles_iff' := λ _, (ne_self_iff_false _).symm }

instance : has_emptyc (indexed_list spec τ) := ⟨empty spec τ⟩

end empty


end indexed_list

end oracle_spec