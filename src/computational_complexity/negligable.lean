import computational_complexity.polynomial_asymptotics

def negligable {α R : Type*} [normed_ring R] [preorder α] (f : α → R) :=
filter.tendsto f filter.at_top (nhds 0)

namespace negligable

end negligable