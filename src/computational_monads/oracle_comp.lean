import computational_monads.oracle_spec

variables {α β γ : Type} {spec spec' : oracle_spec}

open oracle_spec

/-- Type to represent computations with access so oracles specified by and `oracle_spec` -/
inductive oracle_comp (spec : oracle_spec) : Type → Type 1
| pure' (α : Type) (a : α) : oracle_comp α
| bind' (α β : Type) (oa : oracle_comp α) (ob : α → oracle_comp β) : oracle_comp β
| query (i : spec.ι) (t : spec.domain i) : oracle_comp (spec.range i)

namespace oracle_comp

/-- Probabalistic computation is represented as access to α coin-flipping oracle -/
@[reducible, inline]
def coin : oracle_comp coin_oracle bool := oracle_comp.query () ()

section monad

/-- Natural monad structure on `oracle_comp`.
  Simplification lemmas will tend towards `pure` and `bind` over `pure'` and `bind'` -/
instance monad (spec : oracle_spec) : monad (oracle_comp spec) :=
{ pure := oracle_comp.pure', bind := oracle_comp.bind' }

@[simp]
lemma pure'_eq_pure (spec : oracle_spec) (a : α) :
  (pure' α a : oracle_comp spec α) = pure a := rfl

@[simp]
lemma return_eq_pure (spec : oracle_spec) (a : α) :
  (return a : oracle_comp spec α) = pure a := rfl

@[simp]
lemma bind'_eq_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  bind' α β oa ob = (oa >>= ob) := rfl

end monad

/-- Constructing an `oracle_comp` implies the existence of some element of the underlying type.
  The assumption that the range of the oracles is `inhabited` is the key point for this -/
def inhabited_base {spec : oracle_spec} :
  Π {α : Type} (oa : oracle_comp spec α), inhabited α
| _ (pure' α a) := ⟨a⟩
| _ (bind' α β oa ob) := let ⟨a⟩ := inhabited_base oa in inhabited_base (ob a)
| _ (query i t) := ⟨arbitrary (spec.range i)⟩

section support

/-- Set of possible outputs of the computation, allowing for any possible output of the queries.
  This will generally correspond to the support of `eval_distribution`,
    but is slightly more general since it doesn't require α finite range. -/
def support {spec : oracle_spec} : Π {α : Type} (oa : oracle_comp spec α), set α
| _ (pure' α a) := {a}
| _ (bind' α β oa ob) := ⋃ α ∈ oa.support, (ob α).support
| _ (query i t) := ⊤

@[simp]
lemma support_pure (spec : oracle_spec) (a : α) :
  (pure a : oracle_comp spec α).support = {a} := rfl

@[simp]
lemma mem_support_pure_iff (a a' : α) :
  a' ∈ (pure a : oracle_comp spec α).support ↔ a' = a :=
set.mem_singleton_iff

lemma support_pure' (spec : oracle_spec) (a : α) :
  (pure' α a : oracle_comp spec α).support = {a} := rfl

lemma support_return (spec : oracle_spec) (a : α) :
  (return a : oracle_comp spec α).support = {a} := rfl

@[simp]
lemma support_bind (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (oa >>= ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

@[simp]
lemma mem_support_bind_iff (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) (β : β) :
  β ∈ (oa >>= ob).support ↔ ∃ α ∈ oa.support, β ∈ (ob α).support :=
by simp only [support_bind, set.mem_Union]

lemma support_bind' (oa : oracle_comp spec α) (ob : α → oracle_comp spec β) :
  (bind' α β oa ob).support = ⋃ α ∈ oa.support, (ob α).support := rfl

@[simp]
lemma support_bind_bind (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ) :
  (do {α ← oa, β ← ob α, oc α β}).support =
    ⋃ α ∈ oa.support, ⋃ β ∈ (ob α).support, (oc α β).support :=
by simp

@[simp]
lemma mem_support_bind_bind_iff (oa : oracle_comp spec α)
  (ob : α → oracle_comp spec β) (oc : α → β → oracle_comp spec γ) (c : γ) :
  c ∈ (do {α ← oa, β ← ob α, oc α β}).support ↔
    ∃ α ∈ oa.support, ∃ β ∈ (ob α).support, c ∈ (oc α β).support :=
by simp only [support_bind_bind, set.mem_Union]

@[simp]
lemma support_query (i : spec.ι) (t : spec.domain i) :
  (query i t).support = ⊤ := rfl

@[simp]
lemma mem_support_query (i : spec.ι) (t : spec.domain i) (u : spec.range i) :
  u ∈ (query i t).support :=
set.mem_univ u

@[simp]
lemma support_map (f : α → β) (oa : oracle_comp spec α) :
  (f <$> oa).support = f '' oa.support :=
calc (f <$> oa).support = ⋃ α ∈ oa.support, {f α} : rfl
  ... = f '' (⋃ α ∈ oa.support, {α}) : by simp only [set.image_Union, set.image_singleton]
  ... = f '' oa.support : congr_arg (λ _, f '' _) (set.bUnion_of_singleton oa.support)

@[simp]
lemma mem_support_map_iff (f : α → β) (oa : oracle_comp spec α) (β : β) :
  β ∈ (f <$> oa).support ↔ ∃ α ∈ oa.support, f α = β :=
by simp only [support_map, set.mem_image, exists_prop]

example : support (do {
  β ← coin, β' ← coin,
  x ← if β then return 0 else return 1,
  y ← return (if β' then 1 else 0),
  return (x * y)
} : oracle_comp coin_oracle ℕ) = {1, 0} :=
by simp

end support

section decidable

/-- Typeclass for computations that only return values of types with `decidable_eq` instances.
  In this case we can explicitly calculate the `support` as α `finset` rather than α `set`. -/
@[class]
inductive decidable {spec : oracle_spec} : 
  Π {α : Type}, oracle_comp spec α → Type 1
| decidable_pure' (α : Type) (a : α) (h : decidable_eq α) : decidable (pure' α a)
| decidable_bind' (α β : Type) (oa : oracle_comp spec α) (ob : α → oracle_comp spec β)
    (hoa : decidable oa) (hob : ∀ α, decidable (ob α)) : decidable (bind' α β oa ob)
| decidable_query (i : spec.ι) (t : spec.domain i) : decidable (query i t)

open decidable

def decidable.decidable_eq {spec : oracle_spec} [computable spec] :
  Π {α : Type} {oa : oracle_comp spec α}, decidable oa → decidable_eq α
| _ _ (decidable_pure' α a h) := h
| _ _ (decidable_bind' α β oa ob hoa hob) := let ⟨a⟩ := inhabited_base oa in (hob a).decidable_eq
| _ _ (decidable_query i t) := by apply_instance

section fin_support

/-- Compute an explicit `finset` of the elements in `support`. -/
def fin_support {spec : oracle_spec} [spec.computable] [spec.finite_range] :
  Π {α : Type} (oa : oracle_comp spec α), decidable oa → finset α
| _ _ (decidable_pure' α a h) := {a}
| _ _ (decidable_bind' α β oa ob hoa hob) := 
  by haveI : decidable_eq β := (let ⟨a⟩ := inhabited_base oa in (hob a).decidable_eq);
  refine (fin_support oa hoa).bUnion (λ α, fin_support (ob α) (hob α))
| _ _ (decidable_query i t) := finset.univ

lemma mem_fin_support_iff_mem_support {spec : oracle_spec} [spec.computable] [spec.finite_range] :
  Π {α : Type} (oa : oracle_comp spec α) (hoa : decidable oa) (α : α),
    α ∈ (fin_support oa hoa) ↔ α ∈ oa.support
| _ _ (decidable_pure' α a h) α' :=
    by simp [finset.coe_singleton α, support, fin_support]
| _ _ (decidable_bind' α β oa ob hoa hob) b :=
    by simp [fin_support, support, mem_fin_support_iff_mem_support]
| _ _ (decidable_query i t) u :=
    by simp [support, fin_support]

theorem coe_fin_support_eq_support {spec : oracle_spec} [spec.computable] [spec.finite_range]
  {α : Type} (oa : oracle_comp spec α) (hoa : decidable oa) :
    (fin_support oa hoa : set α) = oa.support :=
set.ext (mem_fin_support_iff_mem_support oa hoa)

end fin_support

end decidable

end oracle_comp