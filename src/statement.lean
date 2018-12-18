import .torus .Weil_group .group_cohomology

universes u v w

noncomputable theory
local attribute [instance] classical.prop_decidable

variables {F : Type u} [local_field F]
variables {TR : Type v} [comm_ring TR] {T : algebra F TR} [cogroup T]
variables (ht : torus T) (W : Type w) [Weil_group F W]

attribute [instance] torus.hat.topological_space_additive
attribute [instance] torus.hat.topological_add_group_additive

set_option class.instance_max_depth 10
instance topological_group_module_r_h : topological_group_module
  (relative_Weil_group F W ht.top) (additive ht.hat) :=
sorry


attribute [instance] torus.rat_pt.topological_group
attribute [instance] torus.rat_pt.group
attribute [instance] torus.rat_pt.topological_space
attribute [instance] topological_field.units.topological_space
attribute [instance] units.group
attribute [instance] topological_field.units.topological_group

def local_langlands_torus :
    H1c (relative_Weil_group F W ht.top) (additive ht.hat)
  ≃ topological_group_hom ht.rat_pt (units ℂ) :=
sorry