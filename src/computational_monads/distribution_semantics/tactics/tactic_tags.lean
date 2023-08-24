/-
Copyright (c) 2023 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

/-!
# Tags for Marking Distributional Equivalence Lemmas

This file defines a tactic `pairwise_dist_equiv` for working with and proving instances of
`dist_equiv` between sequenced computations, by splitting the goal into line-by-line equivalences.

TODO: some things in `return` and `bind` files I think.
-/

open interactive interactive.types

/-- Tag for lemmas to be automatically applied by `pairwise_dist_equiv`. -/
meta def simp_dist_equiv : user_attribute :=
{ name := "simp_dist_equiv",
  descr := "Lemmas tagged with this attribute are automatically called by the
              `pairwise_dist_equiv` tactic, similar to the way the `simp` tactic works." }

run_cmd attribute.register "simp_dist_equiv"

meta def get_simp_dist_equiv_lemmas : tactic (list pexpr) :=
do {tagged_d_eqs ← (attribute.get_instances "simp_dist_equiv"),
  t' ← mmap tactic.get_decl tagged_d_eqs,
  d ←  return (list.map declaration.value t'),
  q ← return (list.map pexpr.of_expr d),
  return q
}