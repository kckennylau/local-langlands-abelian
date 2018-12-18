import linear_algebra.dimension
import analysis.topology.topological_structures
import algebra.pi_instances
import field_theory.subfield
import ring_theory.ideal_operations
import .topological_group
import .algebra_tensor

local attribute [instance] classical.prop_decidable

universes u v

set_option eqn_compiler.zeta true

class is_alg_closed_field (F : Type u) [field F] : Prop :=
(alg_closed : ∀ f : polynomial F, f.degree > 1 → ∃ x, f.eval x = 0)

variables {F : Type u} [discrete_field F]

class is_integral {K : Type v} [comm_ring K] (i : algebra F K) : Prop :=
(integral : ∀ x : K, ∃ f : polynomial F, f.monic ∧ polynomial.aeval F i x f = 0)

instance discrete_field_of_subalgebra_of_integral {K : Type v} [discrete_field K] (i : algebra F K)
  [is_integral i] (S : subalgebra i) : discrete_field S := sorry

class is_algebraic_closure {K : Type v} [discrete_field K] (i : algebra F K) extends is_alg_closed_field K, is_integral i : Prop

structure Gal {K : Type v} [comm_ring K] (i : algebra F K) extends K ≃ K :=
(hom : is_ring_hom to_fun)
(fix : ∀ x : F, to_fun (i x) = i x)
attribute [instance] Gal.hom

instance Gal.hom' {K : Type v} [comm_ring K] (i : algebra F K) (f : Gal i) : is_ring_hom f.to_equiv := f.hom

theorem Gal.ext {K : Type v} [comm_ring K] (i : algebra F K) : ∀ f g : Gal i, (∀ x, f.to_equiv x = g.to_equiv x) → f = g
| ⟨_, _, _⟩ ⟨_, _, _⟩ H := by rw Gal.mk.inj_eq; from equiv.ext _ _ H

def is_reduced_comm_ring (R : Type u) [comm_ring R] : Prop :=
(⊥ : ideal R).radical = ⊥

def algebraic_closure_field (F : Type u) [discrete_field F] : Type u := sorry
instance (F : Type u) [discrete_field F] : discrete_field (algebraic_closure_field F) := sorry
def algebraic_closure (F : Type u) [discrete_field F] : algebra F (algebraic_closure_field F) := sorry
instance (F : Type u) [discrete_field F] : is_algebraic_closure (algebraic_closure F) := sorry

-- http://www.math.uconn.edu/~kconrad/blurbs/galoistheory/separable2.pdf
class is_separable (S : subalgebra $ algebraic_closure F) : Prop :=
(separable : is_reduced_comm_ring (S.algebra.mod ⊗ (algebraic_closure F).mod))

variables F
structure finite_Galois_extension : Type u :=
(S : subalgebra $ algebraic_closure F)
(finite : vector_space.dim F S.algebra.mod < cardinal.omega)
(separable : is_separable S)
(proj : Gal (algebraic_closure F) → Gal S.algebra)
(proj_commutes : ∀ f : Gal (algebraic_closure F), ∀ x : S, ((proj f).to_equiv x).1 = f.to_equiv x.1)
attribute [instance] finite_Galois_extension.separable

variables {F}
instance Gal.group {K : Type v} [comm_ring K] (i : algebra F K) : group (Gal i) :=
{ mul := λ f g, ⟨f.to_equiv.trans g.to_equiv,
    @@is_ring_hom.comp _ _ _ f.hom _ _ g.hom,
    λ _, by simp [equiv.trans, f.fix, g.fix]⟩,
  mul_assoc := λ _ _ _, Gal.ext _ _ _ $ λ _, by simp,
  one := ⟨equiv.refl _, is_ring_hom.id, λ _, rfl⟩,
  one_mul := λ _, Gal.ext _ _ _ $ λ _, rfl,
  mul_one := λ _, Gal.ext _ _ _ $ λ _, rfl,
  inv := λ f, ⟨f.to_equiv.symm,
      ⟨show f.to_equiv.symm 1 = 1,
        by rw [equiv.symm_apply_eq, is_ring_hom.map_one f.to_equiv],
      λ x y, show f.to_equiv.symm (x * y) = f.to_equiv.symm x * f.to_equiv.symm y,
        by rw [equiv.symm_apply_eq, is_ring_hom.map_mul f.to_equiv];
          rw [equiv.apply_inverse_apply, equiv.apply_inverse_apply],
      λ x y, show f.to_equiv.symm (x + y) = f.to_equiv.symm x + f.to_equiv.symm y,
        by rw [equiv.symm_apply_eq, is_ring_hom.map_add f.to_equiv];
          rw [equiv.apply_inverse_apply, equiv.apply_inverse_apply]⟩,
    λ x, show f.to_equiv.symm (i x) = i x,
      by rw equiv.symm_apply_eq; from (f.fix x).symm⟩,
  mul_left_inv := λ _, Gal.ext _ _ _ $ λ _,
    equiv.apply_inverse_apply _ _ }

instance Gal.finite_Galois_extension.topological_space (E : finite_Galois_extension F) :
  topological_space (Gal E.S.algebra) := ⊤

instance Gal.finite_Galois_extension.topological_group (E : finite_Galois_extension F) :
  topological_group (Gal E.S.algebra) :=
{ continuous_mul := λ x1 h1, by apply is_open_prod_iff.2; intros x y H;
    refine ⟨{x}, {y}, trivial, trivial, _, _, _⟩; simp; simpa using H,
  continuous_inv := continuous_top }

variables (F)
instance Gal_algebraic_closure.topological_space : topological_space (Gal $ algebraic_closure F) :=
@topological_space.induced _
  (Π E : finite_Galois_extension F, Gal E.S.algebra)
  (λ f E, E.proj f)
  (@Pi.topological_space _ _ (λ _, ⊤))

instance Gal.topological_group : topological_group (Gal $ algebraic_closure F) :=
@topological_group.induced _ _ _ _ _
  (@Pi.topological_group (finite_Galois_extension F) (λ E, Gal E.S.algebra) _ _ _)
  (λ f S, S.proj f)
  (by constructor; intros f g; funext S; apply Gal.ext; intro x;
    apply subtype.eq; have := S.proj_commutes; dsimp at this ⊢;
    change ((S.proj (f * g)).to_equiv x).1 = ((S.proj f * S.proj g).to_equiv x).1;
    dsimp [(*), semigroup.mul, monoid.mul, group.mul]; simp [this])

variables {F}
def subalgebra.Gal {K : Type v} [comm_ring K] {i : algebra F K} (S : subalgebra i) : set (Gal i) :=
{ f | ∀ x ∈ S, f.to_equiv x = x }

instance Gal.intermediate.subgroup {K : Type v} [comm_ring K] {i : algebra F K} (S : subalgebra i) :
  is_subgroup S.Gal :=
{ mul_mem := λ f g H1 H2 x hx,
    show f.to_equiv.trans g.to_equiv x = x,
    by simp [H1 x hx, H2 x hx],
  one_mem := λ x hx, rfl,
  inv_mem := λ f H1 x hx,
    show f.to_equiv.symm x = x,
    by rw equiv.symm_apply_eq; from (H1 x hx).symm }

instance Gal.normal (E : finite_Galois_extension F) :
  normal_subgroup E.S.Gal :=
{ normal := λ f hf g x hx,
    show g.to_equiv.trans (f.to_equiv.trans g.to_equiv.symm) x = x,
    from have _ := E.proj_commutes g ⟨x, hx⟩,
    by simp at this ⊢; rw [← this, hf, this];
      [simp, from (((E.proj g).to_equiv) ⟨x, hx⟩).2] }

instance Gal.intermediate.topological_group (E : finite_Galois_extension F) :
  topological_group E.S.Gal :=
topological_group.induced _ _ subtype.val