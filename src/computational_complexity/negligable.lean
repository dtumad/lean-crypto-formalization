import computational_complexity.polynomial_asymptotics

/-!
# Negligable Growth

This file is a unfinished implementation of a `negligable` predicate on function into normed spaces
-/

def negligable {α R : Type*} [normed_ring R] [preorder α] (f : α → R) :=
filter.tendsto f filter.at_top (nhds 0)

namespace negligable

end negligable