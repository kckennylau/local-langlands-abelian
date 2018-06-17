import linear_algebra.dimension
import analysis.topology.topological_structures
import algebra.pi_instances
import .polynomial .topological_group
import .algebra_tensor

local attribute [instance] classical.prop_decidable
local attribute [instance] comm_ring.to_algebra

universes u v

set_option eqn_compiler.zeta true

class is_alg_closed_field (α : Type u) [field α] : Prop :=
(alg_closed : ∀ f : polynomial α, f.deg > 1 → ∃ x, f.eval α α x = 0)

class field_extension (α : out_param $ Type u) (β : Type v)
  [out_param $ field α] [field β] :=
(f : α → β) [hom : is_ring_hom f]

instance field_extension.to_is_ring_hom (α : Type u) (β : Type v)
  [field α] [field β] [field_extension α β] : is_ring_hom (field_extension.f β) :=
field_extension.hom β

instance field_extension.to_algebra (α : Type u) (β : Type v)
  [field α] [field β] [field_extension α β] : algebra α β :=
{ f := field_extension.f β }

class is_algebraic_field_extension (α : out_param $ Type u) (β : Type v)
  [out_param $ field α] [field β] [field_extension α β] : Prop :=
(algebraic : ∀ x : β, ∃ f : polynomial α, f.eval α β x = 0)

class is_algebraic_closure (α : out_param $ Type u) (β : Type v)
  [field α] [field β] [field_extension α β]
  extends is_alg_closed_field β, is_algebraic_field_extension α β : Prop

instance field_extension.to_vector_space
  (α : Type u) (β : Type v) [field α] [field β] [field_extension α β] :
  vector_space α β :=
{ .. algebra.to_module α β }

class subring (α : Type u) [comm_ring α] (S : set α) : Prop :=
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(neg_mem : ∀ {x}, x ∈ S → -x ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → y ∈ S → x * y ∈ S)
(one_mem : (1:α) ∈ S)

open subring

instance subring.to_comm_ring (α : Type u) [comm_ring α] (S : set α) [subring α S] : comm_ring S :=
{ add            := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x + y, add_mem hx hy⟩,
  add_assoc      := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ add_assoc x y z,
  zero           := ⟨0, eq.subst (add_neg_self (1:α)) $ add_mem (one_mem S) $ neg_mem $ one_mem S⟩,
  zero_add       := λ ⟨x, hx⟩, subtype.eq $ zero_add x,
  add_zero       := λ ⟨x, hx⟩, subtype.eq $ add_zero x,
  neg            := λ ⟨x, hx⟩, ⟨-x, neg_mem hx⟩,
  add_left_neg   := λ ⟨x, hx⟩, subtype.eq $ add_left_neg x,
  add_comm       := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.eq $ add_comm x y,
  mul            := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
  mul_assoc      := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc x y z,
  one            := ⟨1, one_mem S⟩,
  one_mul        := λ ⟨x, hx⟩, subtype.eq $ one_mul x,
  mul_one        := λ ⟨x, hx⟩, subtype.eq $ mul_one x,
  left_distrib   := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ left_distrib x y z,
  right_distrib  := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ right_distrib x y z,
  mul_comm       := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.eq $ mul_comm x y }

class subfield (β : Type v) [field β] (S : set β) extends subring β S : Prop :=
(inv_mem : ∀ {x}, x ∈ S → x⁻¹ ∈ S)

open subfield

instance subfield.to_field (β : Type v) [field β] (S : set β) [subfield β S] : field S :=
{ inv := λ ⟨x, hx⟩, ⟨x⁻¹, inv_mem hx⟩,
  zero_ne_one := λ h, zero_ne_one $ subtype.mk.inj h,
  mul_inv_cancel := λ ⟨x, hx1⟩ hx2, subtype.eq $ mul_inv_cancel (λ h, hx2 $ subtype.eq h),
  inv_mul_cancel := λ ⟨x, hx1⟩ hx2, subtype.eq $ inv_mul_cancel (λ h, hx2 $ subtype.eq h),
  .. subring.to_comm_ring β S }

class is_intermediate_field (α : Type u) (β : Type v)
  [field α] [field β] [field_extension α β] (S : set β)
  extends subfield β S : Prop :=
( range : ∀ x : α, (x:β) ∈ S )

instance is_intermediate_field.to_field_extension (α : Type u) (β : Type v)
  [field α] [field β] [field_extension α β] (S : set β)
  [is_intermediate_field α β S] : field_extension α S :=
{ f := λ x, ⟨x, is_intermediate_field.range S x⟩,
  hom := ⟨λ x y, subtype.eq (algebra.coe_add _ _ _ _),
    λ x y, subtype.eq (algebra.coe_mul _ _ _ _),
    subtype.eq (algebra.coe_one _ _)⟩ }

instance is_intermediate_field.to_field_extension' (α : Type u) (β : Type v)
  [field α] [field β] [field_extension α β] (S : set β)
  [is_intermediate_field α β S] : field_extension S β :=
{ f := subtype.val,
  hom := by constructor; intros; try { cases x, cases y }; refl, }

structure Gal (α : Type u) (β : Type v) [field α] [field β] [field_extension α β] extends β ≃ β :=
( hom : is_ring_hom to_fun )
( fix : ∀ x : α, to_fun (algebra.f β x) = algebra.f β x )

theorem Gal.ext (α : Type u) (β : Type v) [field α] [field β] [field_extension α β] :
  ∀ f g : Gal α β, (∀ x, f.to_equiv x = g.to_equiv x) → f = g
| ⟨_, _, _⟩ ⟨_, _, _⟩ H := by rw Gal.mk.inj_eq; from equiv.ext _ _ H

class is_reduced_comm_ring (R : Type u) [comm_ring R] : Prop :=
(reduced : ∀ r : R, ∀ n : ℕ, r ^ n = 0 → r = 0)

-- http://www.math.uconn.edu/~kconrad/blurbs/galoistheory/separable2.pdf
class is_separable_intermediate_extension
  (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (S : set AC) [is_intermediate_field F AC S] : Prop :=
(separable : is_reduced_comm_ring (tensor_a F S AC))

structure finite_Galois_intermediate_extension
  (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC] :=
( S : set AC )
( intermediate : is_intermediate_field F AC S )
( finite : vector_space.dim F S < cardinal.omega )
( separable : is_separable_intermediate_extension F AC S )
( proj : Gal F AC → Gal F S )
( proj_commutes : ∀ f : Gal F AC, ∀ x : S, ((proj f).to_equiv x).1 = f.to_equiv x.1 )
attribute [instance] finite_Galois_intermediate_extension.intermediate
attribute [instance] finite_Galois_intermediate_extension.separable

-- typeclass inference shortcut
instance finite_Galois_intermediate_extension.to_subfield
  (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (E : finite_Galois_intermediate_extension F AC) :
  subfield _ E.S :=
by apply_instance

instance Gal.topological_space
  (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (E : finite_Galois_intermediate_extension F AC) :
  topological_space (Gal F AC) :=
@topological_space.induced _
  (Π S : finite_Galois_intermediate_extension F AC, Gal F S.S)
  (λ f S, S.proj f)
  (@Pi.topological_space _ _ (λ _, ⊤))

instance Gal.group (α : Type u) (β : Type v) [field α] [field β] [field_extension α β] :
  group (Gal α β) :=
{ mul := λ f g, ⟨f.to_equiv.trans g.to_equiv,
    @@is_ring_hom.comp _ _ _ f.hom _ _ g.hom,
    λ _, by simp [equiv.trans, f.fix, g.fix]⟩,
  mul_assoc := λ _ _ _, Gal.ext _ _ _ _ $ λ _, by simp,
  one := ⟨equiv.refl _, is_ring_hom.id, λ _, rfl⟩,
  one_mul := λ _, Gal.ext _ _ _ _ $ λ _, rfl,
  mul_one := λ _, Gal.ext _ _ _ _ $ λ _, rfl,
  inv := λ f, ⟨f.to_equiv.symm,
      ⟨λ x y, show f.to_equiv.symm (x + y) = f.to_equiv.symm x + f.to_equiv.symm y,
        by symmetry; rw ← equiv.apply_eq_iff_eq_inverse_apply;
          rw @is_ring_hom.map_add _ _ _ _ f.to_equiv f.hom;
          rw [equiv.apply_inverse_apply, equiv.apply_inverse_apply],
      λ x y, show f.to_equiv.symm (x * y) = f.to_equiv.symm x * f.to_equiv.symm y,
        by symmetry; rw ← equiv.apply_eq_iff_eq_inverse_apply;
          rw @is_ring_hom.map_mul _ _ _ _ f.to_equiv f.hom;
          rw [equiv.apply_inverse_apply, equiv.apply_inverse_apply],
      show f.to_equiv.symm 1 = 1,
        by symmetry; rw ← equiv.apply_eq_iff_eq_inverse_apply;
          rw @is_ring_hom.map_one _ _ _ _ f.to_equiv f.hom⟩,
    λ x, show f.to_equiv.symm (algebra.f β x) = algebra.f β x,
      by symmetry; rw ← equiv.apply_eq_iff_eq_inverse_apply;
        from f.fix x⟩,
  mul_left_inv := λ _, Gal.ext _ _ _ _ $ λ _,
    equiv.apply_inverse_apply _ _ }

def Gal.finite_Galois_intermediate_extension.topological_group
  (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (E : finite_Galois_intermediate_extension F AC) :
  topological_group (Gal F E.S) :=
by letI : topological_space (Gal F E.S) := ⊤; from
{ continuous_mul := λ x1 h1, by apply is_open_prod_iff.2; intros x y H;
    refine ⟨{x}, {y}, trivial, trivial, _, _, _⟩; simpa using H,
  continuous_inv := continuous_top,
  .. Gal.group F E.S }

instance Gal.topological_group
  (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC] :
  topological_group (Gal F AC) :=
@topological_group.induced (Gal F AC)
  (Π S : finite_Galois_intermediate_extension F AC, Gal F S.S)
  _
  (@Pi.topological_group
    (finite_Galois_intermediate_extension F AC)
    (λ S, Gal F S.S)
    (λ i, Gal.finite_Galois_intermediate_extension.topological_group _ _ _))
  (λ f S, S.proj f)
  (by constructor; intros f g; funext S; apply Gal.ext; intro x;
    apply subtype.eq; have := S.proj_commutes; dsimp at this ⊢;
    change ((S.proj (f * g)).to_equiv x).1 = ((S.proj f * S.proj g).to_equiv x).1;
    dsimp [(*), semigroup.mul, monoid.mul, group.mul]; simp [this])

def Gal.intermediate (α : Type u) (β : Type v)
  [field α] [field β] [field_extension α β]
  (E : set β) [is_intermediate_field α β E] : set (Gal α β) :=
{ f | ∀ x ∈ E, f.to_equiv x = x }

instance Gal.intermediate.subgroup (α : Type u) (β : Type v)
  [field α] [field β] [field_extension α β]
  (E : set β) [is_intermediate_field α β E] :
  is_subgroup (Gal.intermediate α β E) :=
{ mul_mem := λ f g H1 H2 x hx,
    show f.to_equiv.trans g.to_equiv x = x,
    by simp [H1 x hx, H2 x hx],
  one_mem := λ x hx, rfl,
  inv_mem := λ f H1 x hx,
    show f.to_equiv.symm x = x,
    by symmetry; rw ← equiv.apply_eq_iff_eq_inverse_apply;
      from H1 x hx }

instance Gal.normal (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (E : finite_Galois_intermediate_extension F AC) :
  normal_subgroup (Gal.intermediate F AC E.S) :=
{ normal := λ f hf g x hx,
    show g.to_equiv.trans (f.to_equiv.trans g.to_equiv.symm) x = x,
    from have _ := E.proj_commutes g ⟨x, hx⟩,
    by simp at this ⊢; rw [← this, hf, this];
      [simp, from (((E.proj g).to_equiv) ⟨x, hx⟩).2] }

instance Gal.intermediate.topological_group
  (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (E : finite_Galois_intermediate_extension F AC) :
  topological_group (Gal.intermediate F AC E.S) :=
topological_group.induced _ _ subtype.val