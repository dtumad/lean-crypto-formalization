import crypto_foundations.computational_monads.oracle_comp
import crypto_foundations.computational_monads.dist_sem

open oracle_comp

/-- Wrapper for computations with access to two oracles -/
def oracle_comp_pair (A B A' B' C : Type) :=
oracle_comp (A ⊕ A') (B ⊕ B') C

@[simps]
instance oracle_comp_pair.monad {A B A' B' : Type} :
  monad (oracle_comp_pair A B A' B') :=
{ pure := λ C c, oc_ret (comp.ret c),
  bind := λ A B ca cb, oc_bind ca cb }

@[simp]
instance oracle_comp_pair.monad.return_is_well_formed
  {A B A' B' C : Type} (c : C) :
  (return c : oracle_comp_pair A B A' B' C).is_well_formed :=
oc_ret.is_well_formed (comp.ret c)

namespace oracle_comp_pair

variables {A B A' B' C : Type}

def eval_distribution {S S' : Type}
  (oc : oracle_comp_pair A B A' B' C)
  (s : S) (o : S → A → comp (B × S))
  (s' : S') (o' : S' → A' → comp (B' × S')) :
  comp (C × (S × S')) :=
begin
  refine oc.eval_distribution (s, s') (λ ss' aa', _),
  refine aa'.rec (λ a, _) (λ a', _),
  refine (o ss'.1 a) >>= (λ bs, comp.ret ⟨(sum.inl bs.1), (bs.2, ss'.2)⟩),
  refine (o' ss'.2 a') >>= (λ bs', comp.ret ⟨(sum.inr bs'.1), (ss'.1, bs'.2)⟩),
end

@[simp] 
instance eval_distribution.is_well_formed {S S' : Type}
  (oc : oracle_comp_pair A B A' B' C) [hoc : oc.is_well_formed]
  (s : S) (o : S → A → comp (B × S)) [ho : ∀ s a, (o s a).is_well_formed]
  (s' : S') (o' : S' → A' → comp (B' × S')) [ho' : ∀ s' a', (o' s' a').is_well_formed] :
  (oc.eval_distribution s o s' o').is_well_formed :=
begin
  simp [eval_distribution],
  apply oracle_comp.eval_distribution_is_well_formed oc hoc _ _ (λ _ aa', _),
  cases aa'; simp
end

def query_left (a : A) : oracle_comp_pair A B A' B' (with_bot B) :=
do bb' ← (oc_query (sum.inl a)), 
  return (bb'.rec (λ b, ↑b) (λ _, ⊥))

@[simp]
instance query_left.is_well_formed (a : A) :
  (query_left a : oracle_comp_pair A B A' B' (with_bot B)).is_well_formed :=
by simp [query_left]

def query_right (a' : A') : oracle_comp_pair A B A' B' (with_bot B') :=
do bb' ← (oc_query (sum.inr a')),
  return (bb'.rec (λ _, ⊥) (λ b', ↑b'))

@[simp]
instance query_right.is_well_formed (a' : A') :
  (query_right a' : oracle_comp_pair A B A' B' (with_bot B')).is_well_formed :=
by simp [query_right]

end oracle_comp_pair