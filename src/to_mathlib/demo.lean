import to_mathlib.general

section types_and_expressions

-- Basic expressions
#eval 1 + 1
#eval (2 * 3 + 4 ^ 2) ^ 5
#check 1 + 1

example : 1 + 5 = 6 :=
rfl

-- Type defined based on another type
#eval 3 :: 2 :: 1 :: []
#check 3 :: 2 :: 1 :: []

example : ((1 :: 2 :: []).append (3 :: [])) = 1 :: 2 :: 3 :: [] :=
rfl

-- Type defined based on another type and a specific constant value
#check 3 ::ᵥ 2 ::ᵥ 1 ::ᵥ vector.nil

-- Types are actually constant values themselves
#check Type
#check Type 1

-- Definitions take parameters and return a new type
def length_32_vector (α : Type) : Type := vector α 32
def length_32_vector' : Type → Type := λ α, vector α 32

-- Can make parameters implicit if they can be inferred
def repeat_32_times {α : Type} (x : α) : length_32_vector α :=
vector.repeat x 32

end types_and_expressions

section inductive_types

-- Most basic types are defined inductively
inductive color : Type
| white : color
| red : color
| light (c : color) : color
| mix (c₁ : color) (c₂ : color) : color

-- Namespaces for things
#check color.white
open color
#check white

-- Match on an inductive type to define something in terms of it
def make_lighter : color → color
| white := white
| red := light red
| (light c') := light (light c')
| (mix c₁ c₂) := mix (make_lighter c₁) (make_lighter c₂)

example : make_lighter (mix white red) = mix white (light red) :=
rfl

end inductive_types

section propositions

-- The type of equality is actually `Prop`
#check 1 = 2
#check true
#check false

-- We can create a value of type `true`, but not values of type `false`
-- "Proving" something is true is exactly equivalent to giving a value of it
#check true.intro

-- To "prove" an and statement, give proofs of both of the pieces
#check true ∧ true
example : true ∧ true := and.intro true.intro true.intro
example : true ∧ true := ⟨true.intro, true.intro⟩ -- looks like pair type

#check true ∨ false
example : true ∨ false := or.inl true.intro
example : false ∨ true := or.inr true.intro -- looks like sum type

#check false → true
example : false → true := λ _, true.intro -- looks like function type

#check ¬ false -- `¬ p` is exactly the same as `p → false`
example : ¬ false := λ x, x 

#check true ↔ true -- `p ↔ q` is exactly the same as `(p → q) ∧ (q → p)`
example : true ↔ true := ⟨(λ _, true.intro), (λ _, true.intro)⟩

#check ∃ (n : ℕ), n + 1 = 2 -- also looks like a pair type
example : ∃ (n : ℕ), n + 1 = 2 := ⟨1, rfl⟩

#check ∀ (n : ℕ), n + 1 = 1 + n -- also looks like a function type
example : ∀ (n : ℕ), n + 1 = 1 + n := λ n, add_comm n 1

#check rfl

end propositions

section tactic_proofs

-- Can use tactic programming to write more complicated proofs easily
example (p q r : Prop) : ((p → (q → r)) ∧ (p → q)) → (p → (¬p ∨ r)) :=
begin

  intro h_pqr,
  intro proof_of_p,
  right,
  cases h_pqr with h_pqr h_pq,
  specialize h_pqr proof_of_p,
  apply h_pqr,
  exact h_pq proof_of_p,

end

-- The compiler will just reduce this to a regular value internally
example (p q r : Prop) : ((p → (q → r)) ∧ (p → q)) → (p → (¬p ∨ r)) :=
λ x y, or.inr (x.1 y (x.2 y))

-- `simp` tactic auto applies a number of basic rewrite rules to reduce an expression
example (x : ℕ) : x ∈ (⋃ (n : ℕ), ⋂ (z : ℤ), {x | x * x = (n * 0) * (n ^ 2) + 5} : set ℕ) ↔ x ^ 2 = 5 :=
begin

  simp [pow_two],
end

@[simp] lemma pow_two' {α : Type} [monoid α] (x : α) : x ^ 2 = x * x := pow_two x

-- tag a lemma to add it to the list of `simp` lemmas
example (x : ℕ) : x ∈ (⋃ (n : ℕ), ⋂ (z : ℤ), {x | x * x = (n * 0) * (n ^ 2) + 5} : set ℕ) ↔ x ^ 2 = 5 :=
begin
  
  simp only [mul_zero, pow_two', zero_mul, set.mem_Union,
    set.mem_Inter, set.mem_set_of_eq, forall_const, exists_const],
end

-- `field_simp` reduces multiplication and division in a `field` to normal form
example (x y z w : ℝ) : (x / y) * (y / z)⁻¹ * w = (x * z * w) / (y * y) :=
begin
  field_simp
end

end tactic_proofs