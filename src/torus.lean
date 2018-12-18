import algebra.pi_instances analysis.complex
import .algebra_tensor .monoid_ring .field_extensions

universes u v w

instance subtype.comm_group {α : Type u} [comm_group α] (s : set α) [is_subgroup s] : comm_group s :=
by subtype_instance

noncomputable theory
local attribute [instance] classical.prop_decidable

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_ring R] [comm_ring A] [comm_ring B]
variables (iA : algebra R A) (iB : algebra R B)

open algebra.tensor_product

class cogroup :=
(comul : iA →ₐ iA.tensor_product iA)
(comul_assoc : (aassoc iA iA iA).comp
    ((amap comul (alg_hom.id iA)).comp comul)
  = (amap (alg_hom.id iA) comul).comp comul)
(coone : iA →ₐ algebra.id R)
(comul_coone : (tensor_id iA).comp
    ((amap (alg_hom.id iA) coone).comp comul)
  = alg_hom.id iA)
(coinv : iA →ₐ iA)
(comul_coinv : (arec (alg_hom.id iA) coinv).comp comul
  = iA.of_id.comp coone)

open monoid_ring

variables R
set_option class.instance_max_depth 50
instance group_ring.cogroup (M : Type v) [add_comm_group M] :
  cogroup (monoid_ring.algebra R M) :=
{ comul := eval _ _ _ (λ n, of_monoid R M n ⊗ₜ of_monoid R M n) $
    ⟨λ _ _, by rw [of_monoid_add, tensor_product.mul_def],
    by rw is_add_monoid_monoid_hom.zero (of_monoid R M); refl⟩,
  coone := eval _ _ _ (λ n, 1) ⟨λ _ _, (mul_one 1).symm, rfl⟩,
  comul_assoc := monoid_ring.ext _ _ _ _ _ (λ m,
    by simp only [alg_hom.comp_apply, eval_of_monoid, amap_tmul, aassoc_tmul, alg_hom.id_apply]),
  comul_coone := monoid_ring.ext _ _ _ _ _ (λ m,
    by simp only [alg_hom.comp_apply, eval_of_monoid, amap_tmul, tensor_id_tmul, alg_hom.id_apply];
    exact @one_smul R _ _ _ _ (of_monoid R M m)),
  coinv := eval _ _ _ (λ n, of_monoid R M (-n))
    ⟨λ _ _, by rw [neg_add, of_monoid_add], by rw neg_zero; refl⟩,
  comul_coinv := monoid_ring.ext _ _ _ _ _ (λ m,
    by simp only [alg_hom.comp_apply, eval_of_monoid, arec_tmul, alg_hom.id_apply, algebra.of_id_apply];
    rw [← of_monoid_add, add_neg_self]; refl) }
set_option class.instance_max_depth 32

instance int.add_comm_group : add_comm_group ℤ :=
ring.to_add_comm_group ℤ

def GL₁ⁿ (n : ℕ) : algebra R (monoid_ring R (fin n → ℤ)) :=
monoid_ring.algebra _ _

instance GL₁ⁿ.cogroup (n : ℕ) : cogroup (GL₁ⁿ R n) :=
group_ring.cogroup _ _

def GL₁ : algebra R (monoid_ring R ℤ) :=
monoid_ring.algebra _ _

instance GL₁.cogroup : cogroup (GL₁ R) :=
group_ring.cogroup _ _

variables {R}
class is_cogroup_hom [cogroup iA] [cogroup iB] (f : iA →ₐ iB) : Prop :=
(comul : (cogroup.comul iB).comp f = (amap f f).comp (cogroup.comul iA))

section is_cogroup_hom

--   f(1)
-- = f(1) * 1
-- = f(1) * (f(1) * f(1)⁻¹)
-- = (f(1) * f(1)) * f(1)⁻¹
-- = f(1 * 1) * f(1)⁻¹
-- = f(1) * f(1)⁻¹
-- = 1
/-theorem is_cogroup_hom.coone [cogroup iA] [cogroup iB]
  (f : @alg_hom R A B _ _ _ _ _) [is_cogroup_hom R A B f] :
  (cogroup.coone R B).comp f = cogroup.coone R A :=
have _ := cogroup.comul_coone R A,
calc  (cogroup.coone R B).comp f
    = ((cogroup.coone R B).comp f).comp ((alg_hom.tensor_ring _ _).comp
    ((tensor_a.map (alg_hom.id A) (cogroup.coone R A)).comp (cogroup.comul R A))) : by rw [cogroup.comul_coone R A]; simp
... = _ : _
... = _ : _-/

end is_cogroup_hom

def cogroup_hom [cogroup iA] [cogroup iB] :=
subtype (is_cogroup_hom iA iB)

def GL₁.alg_hom : units iA.mod ≃ alg_hom (GL₁ R) iA :=
equiv.trans (show units A ≃ add_monoid_monoid_hom ℤ A, from
{ to_fun := λ u, ⟨λ n, ((u^n:units A):A),
    λ _ _, by simp [gpow_add], by simp⟩,
  inv_fun := λ f, ⟨f.1 1, f.1 (-1),
    by rw [← f.2.1, add_neg_self, f.2.2],
    by rw [← f.2.1, neg_add_self, f.2.2]⟩,
  left_inv := λ u, units.ext $ by simp; refl,
  right_inv := λ f, subtype.eq $ funext $ λ n,
    by apply int.induction_on n; intros;
      simp at *; simp [f.2.2, f.2.1, gpow_add, *]; refl})
(monoid_ring.UMP _ _ _)

-- needs more lemmas about tensoring
instance cogroup.base_change_left [cogroup iB] :
  cogroup (base_change_left iA iB) := sorry

structure cogroup_iso [cogroup iA] [cogroup iB] :=
(to_fun : iA →ₐ iB)
(inv_fun : iB →ₐ iA)
(left_inverse : ∀ x, inv_fun (to_fun x) = x)
(right_inverse : ∀ x, to_fun (inv_fun x) = x)
[hom : is_cogroup_hom iA iB to_fun]

def torus.is_split {F : Type u} [discrete_field F]
  {TR : Type v} [comm_ring TR] (T : algebra F TR) [cogroup T]
  (E : finite_Galois_extension F)
  (rank : ℕ) :=
cogroup_iso (GL₁ⁿ E.S rank) (base_change_left E.S.algebra T)

structure torus {F : Type u} [discrete_field F]
  {TR : Type v} [comm_ring TR] (T : algebra F TR) [cogroup T] :=
(top : finite_Galois_extension F)
(rank : ℕ)
(splits : torus.is_split T top rank)

variables {F : Type u} [discrete_field F]
variables {TR : Type v} [comm_ring TR] {T : algebra F TR} [cogroup T]
variables (ht : torus T)
include ht

def torus.base_change : algebra ht.top.S (ht.top.S.algebra.mod ⊗ T.mod) :=
base_change_left ht.top.S.algebra T

instance torus.base_change.cogroup : cogroup ht.base_change :=
cogroup.base_change_left _ _

def torus.char : Type (max u v) :=
cogroup_hom (GL₁ ht.top.S) ht.base_change

def torus.cochar : Type (max u v) :=
cogroup_hom ht.base_change (GL₁ ht.top.S)

instance torus.char.add_comm_group : add_comm_group ht.char := sorry
instance torus.cochar.add_comm_group : add_comm_group ht.cochar := sorry

def torus.rat_pt : Type (max u v) :=
T →ₐ algebra.id F

instance torus.rat_pt.topological_space : topological_space ht.rat_pt := sorry
instance torus.rat_pt.group : group ht.rat_pt := sorry
instance torus.rat_pt.topological_group : topological_group ht.rat_pt := sorry

def torus.hat : Type (max u v) :=
add_monoid_monoid_hom ht.cochar (units ℂ)

def torus.hat_to_fun : ht.hat → (ht.cochar → units ℂ) :=
subtype.val

instance torus.hat.comm_group : comm_group ht.hat :=
@subtype.comm_group (ht.cochar → units ℂ)
(@pi.comm_group _ _ $ λ _, units.comm_group)
is_add_monoid_monoid_hom
{ mul_mem := λ f g hf hg,
    ⟨λ x y, show f (x + y) * g (x + y) = (f x * g x) * (f y * g y),
      by rw [hf.1, hg.1, mul_assoc, mul_assoc, mul_left_comm (f y)],
    show f 0 * g 0 = 1, by rw [hf.2, hg.2, mul_one]⟩,
  one_mem := ⟨λ _ _, (mul_one _).symm, rfl⟩,
  inv_mem := λ f hf,
    ⟨λ x y, show (f (x + y))⁻¹ = (f x)⁻¹ * (f y)⁻¹,
      by rw [hf.1, mul_inv],
    show (f 0)⁻¹ = 1, by rw [hf.2, one_inv]⟩ }

instance torus.hat.topological_space : topological_space ht.hat :=
topological_space.induced subtype.val Pi.topological_space

instance torus.hat.is_group_hom_hat_to_fun : is_group_hom ht.hat_to_fun := ⟨λ _ _, rfl⟩

instance torus.hat.topological_group {F : Type u} [discrete_field F]
  {TR : Type v} [comm_ring TR] {T : algebra F TR} [cogroup T]
  (ht : torus T) : topological_group ht.hat :=
@@topological_group.induced _ _ _ _ _ _ ht.hat_to_fun _

instance torus.hat.topological_add_group_additive {F : Type u} [discrete_field F]
  {TR : Type v} [comm_ring TR] {T : algebra F TR} [cogroup T]
  (ht : torus T) : topological_add_group (additive ht.hat) :=
additive.topological_add_group

instance torus.hat.topological_space_additive {F : Type u} [discrete_field F]
  {TR : Type v} [comm_ring TR] {T : algebra F TR} [cogroup T]
  (ht : torus T) : topological_space (additive ht.hat) :=
additive.topological_space
