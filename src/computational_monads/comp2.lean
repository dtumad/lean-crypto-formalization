import to_mathlib
import computational_monads.comp
import computational_monads.oracle_comp

inductive t : Type
| tt : t

class has_is_well_formed (M : Type → Type 1) [monad M] :=
(is_well_formed {A : Type} : M A → Prop)
(support {A : Type} : M A → set A)
(return_is_well_formed {A : Type} (a : A) : (is_well_formed (return a)))
(bind_is_well_formed_of_well_formed {A B : Type} (ma : M A) (mb : A → M B) :
  is_well_formed ma → (∀ a ∈ support ma, is_well_formed (mb a)) →
    is_well_formed (ma >>= mb))

instance has_is_well_formed_comp : has_is_well_formed comp :=
{
  is_well_formed := @comp.is_well_formed,
  support := @comp.support,
  return_is_well_formed := λ A a, true.intro,
  bind_is_well_formed_of_well_formed := λ A B ma mb hma hmb, ⟨hma, hmb⟩
}

class has_evaluation (M : Type → Type 1) [monad M]
  [has_is_well_formed M] :=
(T : Type → Type)
(eval {A : Type} (ma : M A) : has_is_well_formed.is_well_formed ma → T A)

 

inductive oracle_comp' (M : Type → Type 1) [monad M]
  (spec : oracle_comp_spec) : Type → Type 1
| oc_ret {C : Type} (c : M C) : oracle_comp' C
| oc_bind {C D : Type} (oc : oracle_comp' C) (od : C → oracle_comp' D) : oracle_comp' D
| oc_query (i : spec.ι) (a : spec.domain i) : oracle_comp' (spec.range i)

@[simps]
instance oracle_comp'.monad (M : Type → Type 1) [monad M]
  (spec : oracle_comp_spec) :
  monad (oracle_comp' M spec) :=
{ pure := λ C, oracle_comp'.oc_ret ∘ return, 
  bind := λ C D, oracle_comp'.oc_bind }

instance oracle_comp'.has_is_well_formed (M : Type → Type 1) [monad M]
  [has_is_well_formed M] (spec : oracle_comp_spec) : 
  has_is_well_formed (oracle_comp' M spec) :=
{
  is_well_formed := λ A oca, begin
    refine oca.rec_on _ _ _,
    {
      intros,
      exact has_is_well_formed.is_well_formed c,
    },
    {
      intros,
      exact ih_oc ∧ (∀ c, ih_od c)
    },
    {
      intros,
      exact true,
    }
  end,
  support := λ A oca, ⊤,
  return_is_well_formed := begin
    intros,
    simp [],
    exact has_is_well_formed.return_is_well_formed a,
  end,
  bind_is_well_formed_of_well_formed := begin
    intros A B ma mb h h',
    refine ⟨h, λ a, h' a (set.mem_univ a)⟩,
  end,

}


-- instance oracle_comp'.has_is_well_formed (M : Type → Type 1) [monad M]
