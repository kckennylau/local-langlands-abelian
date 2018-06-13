import .polynomial

local attribute [instance] classical.prop_decidable
attribute [instance] field.to_comm_ring

class alg_closed_field (α : Type*) extends field α :=
(alg_closed : ∀ f : polynomial α, f.deg > 1 → ∃ x, f.eval α α x = 0)

class field_extension (α : Type*) (β : Type*) [field α] [field β] extends algebra α β

class algebraic_field_extension (α : Type*) (β : Type*) [field α] [field β] extends field_extension α β :=
(algebraic : ∀ x : β, ∃ f : polynomial α, f.eval α β x = 0)

class algebraic_closure (α : Type*) (β : Type*) [field α] [alg_closed_field β] extends algebraic_field_extension α β
