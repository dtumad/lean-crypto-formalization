import data.vector.basic

import computational_monads.oracle_comp

namespace oracle_comp

open oracle_comp_spec

variables {A B : Type} {spec : oracle_comp_spec}

def repeat_n : Π (oa : oracle_comp spec A) (n : ℕ), oracle_comp spec (vector A n)
| _ 0 := return vector.nil
| oa (n + 1) := do {
  a ← oa,
  as ← repeat_n oa n,
  return (a ::ᵥ as)
}

end oracle_comp