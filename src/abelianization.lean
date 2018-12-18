-- Hausdorff abelianization, i.e.
-- quotient by the closure of the commutator

import group_theory.abelianization
import .topological_group

universes u v

theorem list.prod_map {G : Type u} {H : Type v} [group G] [group H]
  (f : G → H) [is_group_hom f] {L : list G} :
  (L.map f).prod = f L.prod :=
list.rec_on L (eq.symm $ is_group_hom.one f) $ λ hd tl ih,
by simp [ih, is_group_hom.mul f]

def commutator_subgroup (G : Type u) [group G] (S : set G) : set G :=
{ z | ∃ L : list G, (∀ x ∈ L, ∃ p ∈ S, ∃ q ∈ S, x = p * q * p⁻¹ * q⁻¹) ∧ L.prod = z }

instance commutator_subgroup.subgroup
  (G : Type u) [group G] (S : set G) :
  is_subgroup (commutator_subgroup G S) :=
{ mul_mem := λ x y ⟨L1, h1, h2⟩ ⟨L2, h3, h4⟩, ⟨L1 ++ L2,
    list.forall_mem_append.2 ⟨h1, h3⟩,
    by simp [h2, h4]⟩,
  one_mem := ⟨[], by simp⟩,
  inv_mem := λ x ⟨L, h1, h2⟩, ⟨L.reverse.map has_inv.inv,
    λ x hx, let ⟨y, h3, h4⟩ := list.exists_of_mem_map hx in
      let ⟨p, hp, q, hq, h5⟩ := h1 y (list.mem_reverse.1 h3) in
      ⟨q, hq, p, hp, by rw [← h4, h5]; simp [mul_assoc]⟩,
    by rw ← h2; from list.rec_on L (by simp) (λ hd tl ih,
      by rw [list.reverse_cons, list.map_append, list.prod_append, ih]; simp)⟩ }

instance commutator_subgroup.normal_subgroup
  (G : Type u) [group G] (N : set G) [normal_subgroup N] :
  normal_subgroup (commutator_subgroup G N) :=
{ normal := λ x ⟨L, h1, h2⟩ g, ⟨L.map $ λ z, g * z * g⁻¹,
    λ x hx, let ⟨y, h3, h4⟩ := list.exists_of_mem_map hx in
      let ⟨p, hp, q, hq, h5⟩ := h1 y h3 in
      ⟨g * p * g⁻¹, normal_subgroup.normal _ hp _,
      g * q * g⁻¹, normal_subgroup.normal _ hq _,
      by rw [← h4, h5]; simp [mul_assoc]⟩,
    by rw ← h2; from list.rec_on L (by simp) (λ hd tl ih,
      by rw [list.map_cons, list.prod_cons, ih]; simp [mul_assoc])⟩ }

variables (G : Type u) (H : Type v)
variables [topological_space G] [group G] [topological_group G]
variables [topological_space H] [group H] [topological_group H]

def Hausdorff_abelianization : Type u :=
quotient_group.quotient (closure (commutator_subgroup G set.univ))

attribute [elab_as_eliminator] quotient_group.induction_on
instance Hausdorff_abelianization.comm_group : comm_group (Hausdorff_abelianization G) :=
{ mul_comm := λ x y, quotient_group.induction_on x $ λ m,
    quotient_group.induction_on y $ λ n, quotient_group.eq.2 $
    subset_closure ⟨[n⁻¹*m⁻¹*n*m], list.forall_mem_singleton.2
      ⟨n⁻¹, trivial, m⁻¹, trivial, by rw [inv_inv, inv_inv]⟩,
    by rw [list.prod_cons, list.prod_nil, mul_one, mul_inv_rev, ← mul_assoc]⟩,
  .. quotient_group.group _ }

instance Hausdorff_abelianization.topological_space : topological_space (Hausdorff_abelianization G) :=
quotient_group.topological_space _ _

instance Hausdorff_abelianization.topological_group : topological_group (Hausdorff_abelianization G) :=
quotient_group.topological_group _ _

variables {G H}
def Hausdorff_abelianization.map (f : G → H) [hf : is_topological_group_hom f] :
  Hausdorff_abelianization G → Hausdorff_abelianization H :=
quotient_group.map _ _ f $ (closure_subset_iff_subset_of_is_closed $
  continuous_iff_is_closed.1 (is_topological_group_hom.cts f) _ is_closed_closure).2 $
λ x ⟨L, hL, hLx⟩, subset_closure ⟨L.map f,
  λ c hcfL, let ⟨b, hbL, hfbc⟩ := list.exists_of_mem_map hcfL in
    let ⟨p, _, q, _, hb⟩ := hL b hbL in
    ⟨f p, trivial, f q, trivial, by rw [← hfbc, hb];
      simp only [is_group_hom.mul f, is_group_hom.inv f]⟩,
  by rw [list.prod_map f, hLx]⟩

set_option class.instance_max_depth 100
theorem Hausdorff_abelianization.induced.is_topological_group_hom
  (f : G → H) [hf : is_topological_group_hom f] :
  is_topological_group_hom (Hausdorff_abelianization.map f) :=
{ cts := continuous_coinduced_dom $
    show continuous (quotient_group.mk ∘ f),
    from hf.cts.comp continuous_coinduced_rng,
  .. quotient_group.is_group_hom_quotient_lift _ _ _ }