import analysis.topology.topological_structures
import .abelianization .field_extensions

attribute [instance] ring.to_add_comm_group

universes u v w

set_option eqn_compiler.zeta true

class local_field (α : Type u) extends topological_field α :=
(locally_compact : ∀ x : α, ∃ (U : set α) (HU : is_open U) (X : set α) (HX : compact X), x ∈ U ∧ U ⊆ X)
(non_discrete : to_topological_field.to_topological_space ≠ ⊤)

-- very non-trivial
constant Artin_reciprocity (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC] :
topological_group_isomorphism (units F) (Hausdorff_abelianization (Gal F AC))

-- uses Haar measure
instance finite_invariant_intermediate_extension.to_local_field
  (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (E : finite_invariant_intermediate_extension F AC) :
  local_field E.S :=
{ continuous_add := sorry,
  continuous_neg := sorry,
  continuous_mul := sorry,
  continuous_inv := sorry,
  locally_compact := sorry,
  non_discrete := sorry,
  .. (sorry : topological_space E.S) }

-- axiomatization due to Tate
structure Weil_group (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (W : Type w) [topological_space W] [group W] [topological_group W] :=
(ϕ : W → Gal F AC)
(ϕ_hom : is_topological_group_hom ϕ)
(ϕ_dense : closure (set.range ϕ) = set.univ)
(r : Π E : finite_invariant_intermediate_extension F AC,
  topological_group_isomorphism (units E.S)
    (Hausdorff_abelianization (ϕ ⁻¹' (Gal.intermediate F AC E.S))))