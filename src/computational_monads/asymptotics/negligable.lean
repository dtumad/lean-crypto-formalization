import analysis.asymptotics.superpolynomial_decay

/-- `superpolynomial_decay` is a more general definition for more general spaces.
  This definition is meant to provide a cleaner API for cryptography proofs -/
def negligable {α : Type*} [topological_space α] [comm_semiring α]
  (f : ℕ → α) : Prop := 
asymptotics.superpolynomial_decay filter.at_top coe f
