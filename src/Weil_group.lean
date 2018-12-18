import analysis.topology.topological_structures
import .abelianization .field_extensions

attribute [instance] ring.to_add_comm_group

universes u v w

class local_field (α : Type u) extends topological_field α, t2_space α, locally_compact_space α :=
(ne_bot : to_topological_field.to_topological_space ≠ ⊤)

-- very non-trivial
def Artin_reciprocity (F : Type u) [local_field F] :
  topological_group_isomorphism (units F) (Hausdorff_abelianization (Gal (algebraic_closure F))) :=
sorry

-- uses Haar measure
instance finite_Galois_extension.to_local_field
  (F : Type u) [local_field F] (E : finite_Galois_extension F) :
  local_field E.S :=
{ continuous_add := sorry,
  continuous_neg := sorry,
  continuous_mul := sorry,
  continuous_inv := sorry,
  t2 := sorry,
  local_compact_nhds := sorry,
  ne_bot := sorry,
  .. (sorry : topological_space E.S) }

-- axiomatization due to Tate
class Weil_group (F : Type u) [local_field F] (W : Type w)
  extends topological_space W, group W, topological_group W :=
(ϕ : W → Gal (algebraic_closure F))
(ϕ_hom : is_topological_group_hom ϕ)
(ϕ_dense : closure (set.range ϕ) = set.univ)
/-(r : Π E : finite_Galois_intermediate_extension F AC,
  topological_group_isomorphism (units E.S)
    (Hausdorff_abelianization (ϕ ⁻¹' (Gal.intermediate F AC E.S))))-/
-- plus 4 more axioms

attribute [instance] Weil_group.ϕ_hom

def induced_Weil_group (F : Type u) [local_field F]
  (W : Type w) [Weil_group F W]
  (E : finite_Galois_extension F) :
  set W :=
Weil_group.ϕ F ⁻¹' E.S.Gal

set_option class.instance_max_depth 20
instance induced_Weil_group.normal (F : Type u) [local_field F]
  (W : Type w) [Weil_group F W]
  (E : finite_Galois_extension F) :
  normal_subgroup (induced_Weil_group F W E) :=
by letI := Gal_algebraic_closure.topological_space F;
   letI := Gal.group (algebraic_closure F);
   letI := Gal.topological_group F; from
@is_group_hom.preimage_normal W (Gal (algebraic_closure F)) _ _inst_3 (Weil_group.ϕ F) (Weil_group.ϕ_hom F W).to_is_group_hom _ (Gal.normal _)

def relative_Weil_group (F : Type u) [local_field F]
  (W : Type w) [Weil_group F W]
  (E : finite_Galois_extension F) : Type w :=
quotient_group.quotient (commutator_subgroup W (induced_Weil_group F W E))

instance relative_Weil_group.topological_space
  (F : Type u) [local_field F]
  (W : Type w) [Weil_group F W]
  (E : finite_Galois_extension F) :
  topological_space (relative_Weil_group F W E) :=
quotient_group.topological_space _ _

instance relative_Weil_group.group
  (F : Type u) [local_field F]
  (W : Type w) [Weil_group F W]
  (E : finite_Galois_extension F) :
  group (relative_Weil_group F W E) :=
quotient_group.group _

instance relative_Weil_group.topological_group
  (F : Type u) [local_field F]
  (W : Type w) [Weil_group F W]
  (E : finite_Galois_extension F) :
  topological_group (relative_Weil_group F W E) :=
quotient_group.topological_group _ _
