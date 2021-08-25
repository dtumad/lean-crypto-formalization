import computational_monads.oracle_comp

open oracle_comp oracle_comp_spec

def random_simulation_oracle (T U : Type) 
  [decidable_eq T] [fintype U] [inhabited U] :
  simulation_oracle (singleton_spec T U) :=
{ S := list (T × U),
  o := λ _ log t, option.rec_on (log.find (λ tu, t = tu.1)) 
    ((comp.bind (comp.rnd U) (λ u, comp.ret ⟨u, ⟨t, u⟩ :: log⟩)))
    ((λ tu, comp.ret ⟨tu.2, log⟩)),
  oracle_is_well_formed := by apply_instance }

-- @[derive comp.is_well_formed]
-- def oracle_comp.simulate_random_oracle {T U C : Type}
--   [decidable_eq T] [fintype U] [inhabited U]
--   (oc : oracle_comp (oracle_comp_spec.singleton_spec T U) C)
--   [oc.is_well_formed] (log_init : list (T × U)) :=
-- oc.simulate log_init (λ _ log t, 
--   option.rec_on (log.find (λ tu, t = tu.1)) 
--   -- If this isn't in the query log, return a random output and add that to the log
--     (comp.bind (comp.rnd U) (λ u, comp.ret ⟨u, ⟨t, u⟩ :: log⟩))
--     (λ tu, comp.ret ⟨tu.2, log⟩))

-- def random_simulation {T U C : Type} 
--   [decidable_eq T] [fintype U] [inhabited U]
--   (oc : oracle_comp.singleton_oracle_comp T U C) : 
--   comp (C × list (T × U)) :=
-- oc.simulate [] (λ _ log t, 
-- option.rec_on (log.find (λ tu, t = tu.1)) 
--   -- If this isn't in the query log, return a random output and add that to the log
--   (comp.bind (comp.rnd U) (λ u, comp.ret ⟨u, ⟨t, u⟩ :: log⟩))
--   (λ tu, comp.ret ⟨tu.2, log⟩))

-- /-- Oracle access to a uniformly random function `T → U` -/
-- def random_oracle_comp (T U : Type) [decidable_eq T]
--   [fintype U] [inhabited U] :=
-- oracle_comp.singleton_oracle_comp T U

-- variables {T U : Type}
--   [decidable_eq T] [fintype U] [inhabited U]

-- @[derive comp.is_well_formed]
-- def random_oracle_comp.simulate {C : Type}
--   (roc : random_oracle_comp T U C) [roc.is_well_formed]
--   (log_init : list (T × U)) : comp (C × list (T × U)) :=
-- roc.simulate log_init (λ _ log t, 
-- option.rec_on (log.find (λ tu, t = tu.1)) 
--   -- If this isn't in the query log, return a random output and add that to the log
--   (comp.bind (comp.rnd U) (λ u, comp.ret ⟨u, ⟨t, u⟩ :: log⟩))
--   (λ tu, comp.ret ⟨tu.2, log⟩))

-- -- @[simp]
-- -- instance random_oracle_comp.simulate.is_well_formed {C : Type}
-- --   (roc : random_oracle_comp T U C) [roc.is_well_formed]
-- --   (log_init : list (T × U)) :
-- --   (roc.simulate log_init).is_well_formed :=
-- -- begin
-- --   simp [random_oracle_comp.simulate],
-- -- end