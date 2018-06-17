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
instance finite_Galois_intermediate_extension.to_local_field
  (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (E : finite_Galois_intermediate_extension F AC) :
  local_field E.S :=
{ continuous_add := sorry,
  continuous_neg := sorry,
  continuous_mul := sorry,
  continuous_inv := sorry,
  locally_compact := sorry,
  non_discrete := sorry,
  .. (sorry : topological_space E.S) }

attribute [instance] topological_group.to_topological_space

-- axiomatization due to Tate
class Weil_group (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (W : Type w) extends topological_group W :=
(ϕ : W → Gal F AC)
(ϕ_hom : is_topological_group_hom ϕ)
(ϕ_dense : closure (set.range ϕ) = set.univ)
(r : Π E : finite_Galois_intermediate_extension F AC,
  topological_group_isomorphism (units E.S)
    (Hausdorff_abelianization (ϕ ⁻¹' (Gal.intermediate F AC E.S))))
-- plus 4 more axioms

attribute [instance] Weil_group.ϕ_hom

def induced_Weil_group (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (W : Type w) [hw : Weil_group F AC W]
  (E : finite_Galois_intermediate_extension F AC) :
  set W :=
hw.ϕ ⁻¹' (Gal.intermediate F AC E.S)

instance induced_Weil_group.normal (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (W : Type w) [hw : Weil_group F AC W]
  (E : finite_Galois_intermediate_extension F AC) :
  normal_subgroup (induced_Weil_group F AC W E) :=
by letI := Gal.topological_group F AC; from
{ .. @is_group_hom.preimage_normal _ _ _ _ _ _ _ _ }

def relative_Weil_group (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (W : Type w) [hw : Weil_group F AC W]
  (E : finite_Galois_intermediate_extension F AC) : Type w :=
left_cosets (commutator_subgroup W (induced_Weil_group F AC W E))

instance relative_Weil_group.topological_group (F : Type u) [local_field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (W : Type w) [hw : Weil_group F AC W]
  (E : finite_Galois_intermediate_extension F AC) :
  topological_group (relative_Weil_group F AC W E) :=
quotient_group.topological_group _ _