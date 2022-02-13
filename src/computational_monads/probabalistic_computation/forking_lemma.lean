import computational_monads.probabalistic_computation.constructions

namespace prob_comp



variables {A B H : Type}

-- def fork (IG : prob_comp A) (q : ℕ) (bag : finset A)
--   (ca : A ×  prob_comp A)


end prob_comp

-- open_locale nnreal

-- noncomputable theory

-- namespace prob_comp

-- -- TODO: Move this somewhere else
-- section prod

-- def prob_comp.prod {A B : Type} (ca : prob_comp A) (cb : prob_comp B) : prob_comp (A × B) :=
-- do {
--   a ← ca,
--   b ← cb,
--   return (a, b)
-- }

-- infix ` ×× `:80 := prob_comp.prod

-- instance prob_comp.prod.is_well_formed {A B : Type} (ca : prob_comp A) (cb : prob_comp B)
--   [ca.is_well_formed] [cb.is_well_formed] :
--   (ca ×× cb).is_well_formed :=
-- by unfold prob_comp.prod; apply_instance

-- end prod

-- example {n : ℕ} (I I' : fin n.succ)
--   {H : Type} [decidable_eq H] (hs hs' : vector H n.succ) : 
--   decidable (I = 0 ∨ I = I' ∨ hs.nth I = hs.nth I) :=
-- by apply_instance

-- variables {X H SO : Type} [fintype H] [inhabited H] [decidable_eq H]

-- def accepting_probability {q : ℕ} (A : X × (vector H q.succ) → prob_comp (fin q.succ × SO)) 
--   [∀ inp, (A inp).is_well_formed]
--   (input_generator : prob_comp X) [input_generator.is_well_formed] : ℝ≥0 :=
-- (input_generator ×× vector_call (rnd H) q.succ >>= A).Pr_prop (λ o, 0 ≤ o.1)

-- -- TODO: will need `|H| ≥ 2` to have good results about the output
-- -- NOTE: X will usually be `ℕ` to pass in the security parameter
-- -- NOTE: Using `q.succ` everywhere forces the `1 ≤ q` condition (since it becomes `1 ≤ q.succ`)
-- def fork_comp {q : ℕ} (A : X × (vector H q.succ) → prob_comp (fin q.succ × SO)) :
--   X → prob_comp (bool × SO × SO) :=
-- λ x, do {
--   hs ← vector_call (rnd H) q.succ,
--   -- TODO: This is annoying to have to do all the time
--   Iσ ← A (x, hs),
--   -- Generating this way should avoid needing to do index arithmetic on the vector length
--   hs_temp ← vector_call (rnd H) q.succ,
--   hs' ← return (vector.of_fn (λ i, if i < Iσ.1 then hs.nth i else hs_temp.nth i)),
--   (I', σ') ← A (x, hs'),
--   return (if (Iσ.1 = 0 ∨ Iσ.1 ≠ I' ∨ hs.nth Iσ.1 = hs'.nth Iσ.1) then ff else tt, Iσ.2, σ')
-- }

-- instance fork_comp.is_well_formed {q : ℕ} (A : X × (vector H q.succ) → prob_comp (fin q.succ × SO))
--   [∀ inp, (A inp).is_well_formed] (x : X) :
--   (fork_comp A x).is_well_formed :=
-- by simp [fork_comp]

-- lemma forking_lemma {q : ℕ} (A : X × (vector H q.succ) → prob_comp (fin q.succ × SO)) 
--   [∀ inp, (A inp).is_well_formed]
--   (input_generator : prob_comp X) [input_generator.is_well_formed] :
--   (input_generator >>= fork_comp A).Pr_prop (λ x, x.1 = tt) ≥
--     let acc := (accepting_probability A input_generator)
--       in acc * ((acc / q) - (1 / fintype.card H)) :=
-- begin
--   simp [fork_comp, accepting_probability, -vector_call_succ],
--   
-- end


-- end prob_comp 