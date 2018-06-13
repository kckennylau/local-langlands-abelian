import analysis.topology.topological_structures
import .abelianization

attribute [instance] ring.to_add_comm_group

class local_field (α : Type*) extends t : topological_space α, field α, topological_ring α :=
(locally_compact : ∀ x : α, ∃ (U : set α) (HU : is_open U) (X : set α) (HX : compact X), x ∈ U ∧ U ⊆ X)
(non_discrete : t ≠ ⊤)