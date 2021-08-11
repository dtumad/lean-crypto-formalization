import crypto_foundations.computational_monads.oracle_comp

/-- Oracle access to a random function -/
def random_oracle_comp (T U : Type) [decidable_eq T]
  [fintype U] [inhabited U] :=
oracle_comp.singleton_oracle_comp T U

variables {T U : Type}
  [decidable_eq T] [fintype U] [inhabited U]

def random_oracle_comp.eval_distribution {C : Type}
  (roc : random_oracle_comp T U C) : comp (C × list (T × U)) :=
roc.eval_distribution [] (λ _ log t, 
option.rec_on (log.find (λ tu, t = tu.1)) 
  -- If this isn't in the query log, return a random output and add that to the log
  (comp.bind (comp.rnd U) (λ u, comp.ret ⟨u, ⟨t, u⟩ :: log⟩))
  (λ tu, comp.ret ⟨tu.2, log⟩))