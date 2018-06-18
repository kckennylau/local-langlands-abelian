import .torus .Weil_group .group_cohomology

universes u v w

variables (F : Type u) [local_field F]
variables (AC : Type v) [field AC] [is_alg_closed_field AC]
variables [field_extension F AC] [is_algebraic_closure F AC]
variables (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
variables (ht : torus F AC T) (W : Type w) [Weil_group F AC W]

instance : topological_group_module
  (relative_Weil_group F AC W (ht.split))
  (torus.hat F AC T ht) :=
sorry

attribute [instance] torus.rat_pt.topological_group
attribute [instance] topological_field.units.topological_group

def local_langlands_torus :
    H1c (relative_Weil_group F AC W ht.split) (torus.hat F AC T ht)
  ≃ topological_group_hom (torus.rat_pt F AC T ht) (units ℂ) :=
sorry