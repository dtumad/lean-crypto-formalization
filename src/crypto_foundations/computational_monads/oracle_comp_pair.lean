-- import crypto_foundations.computational_monads.oracle_comp
-- import crypto_foundations.computational_monads.dist_sem

-- open oracle_comp

-- namespace oracle_comp_sum

-- variables {A A' B B' C S : Type}

-- /-- 
--   Note that while `o` and `o'` 'share' the same state type `S`,
--     this type can itself be instantiated to a `sum` type to seperate them -/
-- def eval_distribution_sum (oc : oracle_comp (A ⊕ A') (B ⊕ B') C)
--   (s : S) (o : S → A → comp (B × S)) (o' : S → A' → comp (B' × S)) :
--   comp (C × S) :=
-- begin
--   refine oc.eval_distribution s (λ s, _),
--   refine sum.elim (λ a, _) (λ a', _),
--   refine functor.map (prod.map sum.inl id) (o s a),
--   refine functor.map (prod.map sum.inr id) (o' s a'),
-- end

-- @[simp]
-- instance eval_distribution_sum.is_well_formed 
--   (oc : oracle_comp (A ⊕ A') (B ⊕ B') C) [hoc : oc.is_well_formed]
--   (s : S) (o : S → A → comp (B × S)) (o' : S → A' → comp (B' × S)) 
--   [∀ s a, (o s a).is_well_formed] [∀ s a', (o' s a').is_well_formed] :
--   (eval_distribution_sum oc s o o').is_well_formed :=
-- oracle_comp.eval_distribution_is_well_formed oc hoc
--   _ _ (λ s, by simp [sum.forall])

-- def query_sum_left (A A' B B' : Type) (a : A) : 
--   oracle_comp (A ⊕ A') (B ⊕ B') (with_bot B) :=
-- functor.map (sum.elim some (function.const B' ⊥)) (oc_query (sum.inl a))

-- @[simp]
-- instance query_sum_left.is_well_formed (a : A) :
--   (query_sum_left A A' B B' a).is_well_formed :=
-- by simp [query_sum_left]

-- -- lemma eval_distribution_sum_query_sum_left (a : A) --[hoc : oc.is_well_formed]
-- --   (s : S) (o : S → A → comp (B × S)) (o' : S → A' → comp (B' × S)) 
-- --   [∀ s a, (o s a).is_well_formed] [∀ s a', (o' s a').is_well_formed] :
-- --   eval_distribution_sum (query_sum_left A A' B B' a)


-- def query_right (a' : A') : oracle_comp (A ⊕ A') (B ⊕ B') (with_bot B') :=
-- do bb' ← (oc_query (sum.inr a')),
--   return (bb'.rec (λ _, ⊥) (λ b', ↑b'))

-- @[simp]
-- instance query_right.is_well_formed (a' : A') :
--   (query_right a' : oracle_comp (A ⊕ A') (B ⊕ B') (with_bot B')).is_well_formed :=
-- by simp [query_right]

-- end oracle_comp_sum

-- -- /-- Wrapper for computations with access to two oracles -/
-- -- def oracle_comp_pair (A B A' B' C : Type) :=
-- -- oracle_comp (A ⊕ A') (B ⊕ B') C

-- -- @[simps]
-- -- instance oracle_comp_pair.monad {A B A' B' : Type} :
-- --   monad (oracle_comp_pair A B A' B') :=
-- -- { pure := λ C c, oc_ret (comp.ret c),
-- --   bind := λ A B ca cb, oc_bind ca cb }

-- -- @[simp]
-- -- instance oracle_comp_pair.monad.return_is_well_formed
-- --   {A B A' B' C : Type} (c : C) :
-- --   (return c : oracle_comp_pair A B A' B' C).is_well_formed :=
-- -- oc_ret.is_well_formed (comp.ret c)

-- namespace oracle_comp_pair

-- variables {A B A' B' C : Type}

-- def eval_distribution' {S S' : Type}
--   (oc : oracle_comp (A ⊕ A') (B ⊕ B') C)
--   (s : S) (o : S → A → comp (B × S))
--   (s' : S') (o' : S' → A' → comp (B' × S')) :
--   comp (C × (S × S')) :=
-- oc.eval_distribution (s, s') (λ ss', (sum.elim 
--   (functor.map (λ bs, ⟨sum.inl bs.1, bs.2, ss'.2⟩))
--   (functor.map (λ bs, ⟨sum.inr bs.1, ss'.1, bs.2⟩))
--     : comp (B × S) ⊕ comp (B' × S') → comp ((B ⊕ B') × S × S'))
--   ∘ (sum.map (o ss'.1) (o' ss'.2)))

-- @[simp] 
-- instance eval_distribution.is_well_formed {S S' : Type}
--   (oc : oracle_comp (A ⊕ A') (B ⊕ B') C) [hoc : oc.is_well_formed]
--   (s : S) (o : S → A → comp (B × S)) [ho : ∀ s a, (o s a).is_well_formed]
--   (s' : S') (o' : S' → A' → comp (B' × S')) [ho' : ∀ s' a', (o' s' a').is_well_formed] :
--   (eval_distribution' oc s o s' o').is_well_formed :=
-- begin
--   simp [eval_distribution'],
--   apply oracle_comp.eval_distribution_is_well_formed oc hoc _ _ (λ _ aa', _),
--   cases aa'; simp
-- end

-- def query_left (a : A) : oracle_comp (A ⊕ A') (B ⊕ B') (with_bot B) :=
-- do bb' ← (oc_query (sum.inl a)), 
--   return (bb'.rec (λ b, ↑b) (λ _, ⊥))

-- @[simp]
-- instance query_left.is_well_formed (a : A) :
--   (query_left a : oracle_comp (A ⊕ A') (B ⊕ B') (with_bot B)).is_well_formed :=
-- by simp [query_left]

-- lemma eval_distribution_query_left {S S' : Type} [decidable_eq S']
--   (a : A)
--   (s : S) (s' : S') (o : S → A → comp (B × S)) [ho : ∀ s a, (o s a).is_well_formed]
--   (o' : S' → A' → comp (B' × S')) [ho' : ∀ s' a', (o' s' a').is_well_formed]
--   (b : B) (out_s : S) (out_s' : S') :
--   (comp.eval_distribution (eval_distribution' (query_left a) s o s' o')) (b, out_s, out_s') = 
--     if out_s' = s' then (o s a).eval_distribution (b, out_s) else 0 :=
-- begin
--   split_ifs; sorry,  
-- end

-- def query_right (a' : A') : oracle_comp (A ⊕ A') (B ⊕ B') (with_bot B') :=
-- do bb' ← (oc_query (sum.inr a')),
--   return (bb'.rec (λ _, ⊥) (λ b', ↑b'))

-- @[simp]
-- instance query_right.is_well_formed (a' : A') :
--   (query_right a' : oracle_comp (A ⊕ A') (B ⊕ B') (with_bot B')).is_well_formed :=
-- by simp [query_right]

-- end oracle_comp_pair