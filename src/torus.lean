import algebra.pi_instances
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

def cogroup.base_change_left [cogroup R B] :
  @cogroup A _ (tensor_a R A B) _ (base_change_left _ _ _) :=
sorry

structure cogroup_iso [cogroup R A] [cogroup R B] extends A ≃ B :=
(to_is_alg_hom : is_alg_hom to_fun)
(hom : is_cogroup_hom R A B ⟨to_fun, to_is_alg_hom⟩)

#check λ (F : Type u) [field F]
  (AC : Type v) [field AC] [is_alg_closed_field AC]
  [field_extension F AC] [is_algebraic_closure F AC]
  (T : Type w) [comm_ring T] [algebra F T] [cogroup F T]
(split : finite_Galois_intermediate_extension F AC)
(rank : ℕ),
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
(splits :
  @cogroup_iso split.S _ (tensor_a F split.S T)
  (tensor_a.comm_ring _ _ _)
  (base_change_left F split.S T)
  (GL₁ⁿ split.S rank) _ _
  (cogroup.base_change_left F split.S T)
  (GL₁ⁿ.cogroup _ _))