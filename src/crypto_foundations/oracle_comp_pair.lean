import crypto_foundations.oracle_comp

open oracle_comp

def oracle_comp_pair (A B A' B' C : Type) :=
oracle_comp (A ⊕ A') (B ⊕ B') C

@[simps]
instance oracle_comp_pair.monad {A B A' B' : Type} :
  monad (oracle_comp_pair A B A' B') :=
{ pure := λ C c, oc_ret (comp.ret c),
  bind := λ A B ca cb, oc_bind ca cb }

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

def query_left (a : A) : oracle_comp_pair A B A' B' (with_bot B) :=
do bb' ← (oc_query (sum.inl a)), 
  return (bb'.rec (λ b, ↑b) (λ _, ⊥))

def query_right (a' : A') : oracle_comp_pair A B A' B' (with_bot B') :=
do bb' ← (oc_query (sum.inr a')),
  return (bb'.rec (λ _, ⊥) (λ b', ↑b'))

end oracle_comp_pair