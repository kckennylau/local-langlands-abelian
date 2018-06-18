import algebra.pi_instances analysis.complex
import .algebra_tensor .monoid_ring .field_extensions

universes u v w u₁

set_option eqn_compiler.zeta true

noncomputable theory
local attribute [instance] classical.prop_decidable

variables (R : Type u) [comm_ring R]
variables (A : Type v) [comm_ring A] [algebra R A]
variables (B : Type w) [comm_ring B] [algebra R B]

section cogroup

local attribute [instance] comm_ring.to_algebra

class cogroup :=
(comul : alg_hom A (tensor_a R A A))
(comul_assoc : (alg_hom.tensor_assoc R A A A).comp
    ((tensor_a.map comul (alg_hom.id A)).comp comul)
  = (tensor_a.map (alg_hom.id A) comul).comp comul)
(coone : alg_hom A R)
(comul_coone : (alg_hom.tensor_ring _ _).comp
    ((tensor_a.map (alg_hom.id A) coone).comp comul)
  = alg_hom.id A)
(coone_comul : (alg_hom.ring_tensor _ _).comp
    ((tensor_a.map coone (alg_hom.id A)).comp comul)
  = alg_hom.id A)
(coinv : alg_hom A A)
(comul_coinv : ((tensor_a.UMP R A A _).1 (alg_hom.id A, coinv)).comp comul
  = (alg_hom.f A).comp coone)
(coinv_comul : ((tensor_a.UMP R A A _).1 (coinv, alg_hom.id A)).comp comul
  = (alg_hom.f A).comp coone)

end cogroup

open monoid_ring

attribute [instance] add_comm_group.to_add_comm_monoid

instance group_ring.cogroup (M : Type v) [add_comm_group M] :
  cogroup R (monoid_ring R M) :=
{ comul := (monoid_ring.UMP R M _).1
    ⟨λ n, (of_monoid _ _ n) ⊗ₛ (of_monoid _ _ n),
    λ _ _, by simp [is_add_monoid_monoid_hom.add (of_monoid R M), tensor_a.mul_def],
    by simp [is_add_monoid_monoid_hom.zero (of_monoid R M), tensor_a.one_def]⟩,
  comul_assoc := by apply ((monoid_ring.UMP R M _).symm.apply_eq_iff_eq _ _).1;
    apply subtype.eq; funext n; simp,
  coone := by letI := comm_ring.to_algebra R; from
    (monoid_ring.UMP R M _).1 ⟨λ _, 1, by simp, rfl⟩,
  comul_coone := by apply ((monoid_ring.UMP R M _).symm.apply_eq_iff_eq _ _).1;
    apply subtype.eq; funext n; simp,
  coone_comul := by apply ((monoid_ring.UMP R M _).symm.apply_eq_iff_eq _ _).1;
    apply subtype.eq; funext n; simp,
  coinv := (monoid_ring.UMP R M _).1
    ⟨λ n, of_monoid _ _ (-n),
    λ _ _, by simp [is_add_monoid_monoid_hom.add (of_monoid R M)],
    by simp [is_add_monoid_monoid_hom.zero (of_monoid R M)]⟩,
  comul_coinv := by apply ((monoid_ring.UMP R M _).symm.apply_eq_iff_eq _ _).1;
    apply subtype.eq; funext _; simp;
    rw [← is_add_monoid_monoid_hom.add (of_monoid R M)];
    simp [is_add_monoid_monoid_hom.zero (of_monoid R M)],
  coinv_comul := by apply ((monoid_ring.UMP R M _).symm.apply_eq_iff_eq _ _).1;
    apply subtype.eq; funext _; simp;
    rw [← is_add_monoid_monoid_hom.add (of_monoid R M)];
    simp [is_add_monoid_monoid_hom.zero (of_monoid R M)] }

instance int.add_comm_group : add_comm_group ℤ :=
ring.to_add_comm_group ℤ

@[reducible] def GL₁ⁿ (n : ℕ) : Type u :=
monoid_ring R (fin n → ℤ)

instance GL₁ⁿ.algebra (n : ℕ) : algebra R (GL₁ⁿ R n) :=
by apply_instance

instance GL₁ⁿ.cogroup (n : ℕ) : cogroup R (GL₁ⁿ R n) :=
by apply_instance

@[reducible] def GL₁ : Type u :=
monoid_ring R ℤ

instance GL₁.cogroup : cogroup R (GL₁ R) :=
by apply_instance

class is_cogroup_hom [cogroup R A] [cogroup R B]
  (f : @alg_hom R A B _ _ _ _ _) : Prop :=
(comul : (cogroup.comul R B).comp f = (tensor_a.map f f).comp (cogroup.comul R A))

section is_cogroup_hom

local attribute [instance] comm_ring.to_algebra

--   f(1)
-- = f(1) * 1
-- = f(1) * (f(1) * f(1)⁻¹)
-- = (f(1) * f(1)) * f(1)⁻¹
-- = f(1 * 1) * f(1)⁻¹
-- = f(1) * f(1)⁻¹
-- = 1
/-theorem is_cogroup_hom.coone [cogroup R A] [cogroup R B]
  (f : @alg_hom R A B _ _ _ _ _) [is_cogroup_hom R A B f] :
  (cogroup.coone R B).comp f = cogroup.coone R A :=
have _ := cogroup.comul_coone R A,
calc  (cogroup.coone R B).comp f
    = ((cogroup.coone R B).comp f).comp ((alg_hom.tensor_ring _ _).comp
    ((tensor_a.map (alg_hom.id A) (cogroup.coone R A)).comp (cogroup.comul R A))) : by rw [cogroup.comul_coone R A]; simp
... = _ : _
... = _ : _-/

end is_cogroup_hom

def cogroup_hom [cogroup R A] [cogroup R B] :=
subtype (is_cogroup_hom R A B)

def GL₁.alg_hom : units A ≃ alg_hom (GL₁ R) A :=
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
instance cogroup.base_change_left [cogroup R B] :
  @cogroup A _ (tensor_a R A B) _ (base_change_left _ _ _) :=
sorry

structure cogroup_iso [cogroup R A] [cogroup R B] extends A ≃ B :=
(to_is_alg_hom : is_alg_hom to_fun)
(hom : is_cogroup_hom R A B ⟨to_fun, to_is_alg_hom⟩)

def torus.is_split (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (split : finite_Galois_intermediate_extension F AC)
  (rank : ℕ) :=
@cogroup_iso split.S _ (tensor_a F split.S T)
  (tensor_a.comm_ring _ _ _)
  (base_change_left F split.S T)
  (GL₁ⁿ split.S rank) _ _
  (cogroup.base_change_left F split.S T)
  (GL₁ⁿ.cogroup _ _)

structure torus (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T] :=
(split : finite_Galois_intermediate_extension F AC)
(rank : ℕ)
(splits : torus.is_split F AC T split rank)

--set_option trace.class_instances true
def torus.base_change (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) : Type (max v w) :=
tensor_a F ht.split.S T

instance torus.base_change.comm_ring (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) :
  comm_ring (torus.base_change F AC T ht) :=
tensor_a.comm_ring _ _ _

instance torus.base_change.algebra (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) :
  algebra ht.split.S (torus.base_change F AC T ht) :=
base_change_left _ _ _

instance torus.base_change.cogroup (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) :
  cogroup ht.split.S (torus.base_change F AC T ht) :=
cogroup.base_change_left _ _ _

def torus.char (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) :=
cogroup_hom ht.split.S (GL₁ ht.split.S) (torus.base_change F AC T ht)

def torus.co_char (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) :=
cogroup_hom ht.split.S (GL₁ ht.split.S) (torus.base_change F AC T ht)

instance torus.co_char.add_comm_group (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) : add_comm_group (torus.co_char F AC T ht) :=
sorry

def torus.rat_pt (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) :=
@alg_hom F T F _ _ _ _ (comm_ring.to_algebra F)

instance torus.rat_pt.topological_group (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) : topological_group (torus.rat_pt F AC T ht) :=
sorry

def torus.hat (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) :=
{ f : torus.co_char F AC T ht → units ℂ //
    ∀ x y, f (x + y) = f x * f y }

instance : comm_group (units ℂ) :=
{ mul_comm := λ x y, units.ext $ by simp [mul_comm],
  .. (by apply_instance : group (units ℂ)) }

instance torus.hat.is_subgroup (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) : is_subgroup (λ (f : torus.co_char F AC T ht → units ℂ),
    ∀ (x y : torus.co_char F AC T ht), f (x + y) = f x * f y) :=
{ mul_mem := λ f g hf hg x y,
    show f (x + y) * g (x + y) = (f x * g x) * (f y * g y),
    by simp [hf x y, hg x y]; ac_refl,
  one_mem := λ x y, one_mul 1,
  inv_mem := λ f hf x y,
    show (f (x + y))⁻¹ = (f x)⁻¹ * (f y)⁻¹,
    by simp [hf x y, mul_comm] }

instance torus.hat.group (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) : group (torus.hat F AC T ht) :=
subtype.group

instance torus.hat.topological_group (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
  (ht : torus F AC T) : topological_group (torus.hat F AC T ht) :=
topological_group.induced _ _ subtype.val