import algebra.pi_instances
import .algebra_tensor .monoid_ring

universes u v

noncomputable theory
local attribute [instance] classical.prop_decidable

variables (R : Type u) [comm_ring R]
variables (A : Type v) [comm_ring A] [algebra R A]

section cogroup

local attribute [instance] comm_ring.to_algebra

class cogroup :=
(comul : alg_hom A (tensor_a R A A))
(comul_assoc : (alg_hom.tensor_assoc R A A A).comp
    ((tensor_a.map R _ _ _ _ comul (alg_hom.id A)).comp comul)
  = (tensor_a.map R _ _ _ _ (alg_hom.id A) comul).comp comul)
(coone : alg_hom A R)
(comul_coone : (alg_hom.tensor_ring _ _).comp
    ((tensor_a.map R _ _ _ _ (alg_hom.id A) coone).comp comul)
  = alg_hom.id A)
(coone_comul : (alg_hom.ring_tensor _ _).comp
    ((tensor_a.map R _ _ _ _ coone (alg_hom.id A)).comp comul)
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

instance GL₁ⁿ.cogroup (n : ℕ) : cogroup R (GL₁ⁿ R n) :=
by apply_instance

@[reducible] def GL₁ : Type u :=
monoid_ring R ℤ

instance GL₁.cogroup : cogroup R (GL₁ R) :=
by apply_instance