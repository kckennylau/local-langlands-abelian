-- Hausdorff abelianization, i.e.
-- quotient by the closure of the commutator

import group_theory.coset
import .topological_group
import .quotient_group

universes u v

set_option eqn_compiler.zeta true

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
      by rw [list.reverse_cons', list.map_append, list.prod_append, ih]; simp)⟩ }

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

def Hausdorff_abelianization (G : Type u) [topological_group G] : Type u :=
left_cosets (closure (commutator_subgroup G set.univ))

def Hausdorff_abelianization.setoid (G : Type u)
  [topological_group G] : setoid G :=
left_rel (closure (commutator_subgroup G set.univ))

local attribute [instance] Hausdorff_abelianization.setoid

instance Hausdorff_abelianization.comm_group (G : Type u)
  [topological_group G] : comm_group (Hausdorff_abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂ x y $ λ m n,
    quotient.sound $ subset_closure ⟨[n⁻¹*m⁻¹*n*m],
      by simp; refine ⟨n⁻¹, m⁻¹, _⟩; simp,
      by simp [mul_assoc]⟩,
  .. quotient_group.group _ }

instance Hausdorff_abelianization.topological_group (G : Type u)
  [topological_group G] : topological_group (Hausdorff_abelianization G) :=
quotient_group.topological_group _ _

instance Hausdorff_abelianization.topological_space' (G : Type u)
  [topological_group G] : topological_space (quotient (Hausdorff_abelianization.setoid G)) :=
(Hausdorff_abelianization.topological_group G).to_topological_space

def Hausdorff_abelianization.induced {G : Type u} {H : Type v}
  [topological_group G] [topological_group H]
  (f : G → H) [hf : is_topological_group_hom f] :
  Hausdorff_abelianization G → Hausdorff_abelianization H :=
quotient_group.lift _ (quotient.mk ∘ f) $ λ x hx,
have H1 : _ := image_closure_subset_closure_image hf.cts
  ⟨x, hx, rfl⟩,
eq.symm $ quotient.sound $ show 1⁻¹ * f x ∈ _, by simp;
  refine closure_mono (λ z H2, _) H1;
  rcases H2 with ⟨y, ⟨L, h3, h4⟩, h5⟩;
  refine ⟨L.map f,
    (λ c h5, let ⟨b, h6, h7⟩ := list.exists_of_mem_map h5 in
      let ⟨p, _, q, _, h8⟩ := h3 b h6 in
      ⟨f p, trivial, f q, trivial, by rw [← h7, h8];
        simp [is_group_hom.mul f, is_group_hom.inv f]⟩),
    _⟩; simp [list.prod_map f, h4, h5]

def Hausdorff_abelianization.induced.is_topological_group_hom {G : Type u} {H : Type v}
  [topological_group G] [topological_group H]
  (f : G → H) [hf : is_topological_group_hom f] :
  is_topological_group_hom (Hausdorff_abelianization.induced f) :=
{ cts := continuous_coinduced_dom $
    show continuous (quotient.mk ∘ f),
    from hf.cts.comp continuous_coinduced_rng,
  .. quotient_group.lift.is_group_hom _ _ _ }