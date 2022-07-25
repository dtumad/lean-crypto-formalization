import computability.tm_computable

section poly_time

open turing computability

/-- A function is computable in polynomial time if there is a polynomial time implementation.
  In particular this definition is extensional, so the definition of the function isn't important,
  as long as there is a Turing machine implementing the same input/output behaviour. -/
def poly_time {α β : Type} (f : α → β) :=
Σ (ea : fin_encoding α) (eb : fin_encoding β),
  tm2_computable_in_poly_time ea eb f

noncomputable lemma poly_time_id (α : Type) (ea : fin_encoding α) : poly_time (id : α → α) :=
⟨ea, ea, id_computable_in_poly_time ea⟩

end poly_time