import computational_monads.comp
import computational_monads.dist_sem
import to_mathlib

universes u v w

/-- Experimenting with general framework for `comp`, `oracle_comp`, etc. -/

class computation (M : Type u → Type v) [monad M] :=
(is_well_formed {T : Type u} : M T → Prop)
(is_well_formed_ret {T : Type u} (t : T) : is_well_formed (return t))
(is_well_formed_bind {T U : Type u} (mt : M T) (mu : T → M U) :
  is_well_formed mt → (∀ t, is_well_formed $ mu t) → is_well_formed (bind mt mu))

def is_well_formed {M : Type u → Type v} [monad M] [computation M]
  {T : Type u} (ct : M T) : Prop :=
computation.is_well_formed ct

instance comp.computation : computation comp :=
{ is_well_formed := @comp.is_well_formed,
  is_well_formed_ret := λ T t, by simp,
  is_well_formed_bind := λ T U mt mu hmt hmu, by simp [hmt, hmu] }

class has_eval (M : Type u → Type v) [monad M] [computation M] :=
(semant : Type u → Type w)
(eval {T : Type*} (ct : M T) : 
  computation.is_well_formed ct → semant T)

noncomputable instance comp.has_eval : has_eval comp :=
{
  semant := λ T, pmf T,
  eval := λ T ct hct, @comp.eval_distribution T ct hct
}
