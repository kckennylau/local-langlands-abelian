-- in this construction we do not care about the polynomials
-- we only want its universal mapping property

import data.finsupp data.equiv
import .monoid_ring

universes u v

def ℕ.UMP (R : Type u) [ring R] :
  R ≃ add_monoid_monoid_hom ℕ R :=
{ to_fun := λ r, ⟨λ n, r^n, pow_add r, rfl⟩,
  inv_fun := λ f, f.1 1,
  left_inv := λ r, pow_one r,
  right_inv := λ f, subtype.eq $ funext $ λ n,
    nat.rec_on n (by simp [f.2.zero]) $ λ n ih,
    by simp [pow_succ'] at ih ⊢;
    rw [ih, ← f.2.add], }

variables (R : Type u) [decidable_eq R] [comm_ring R]

def polynomial : Type u := monoid_ring R ℕ

instance polynomial.comm_ring : comm_ring (polynomial R) :=
monoid_ring.comm_ring _ _

instance polynomial.algebra : algebra R (polynomial R) :=
monoid_ring.algebra _ _

def polynomial.eval (A : Type v) [comm_ring A] [algebra R A]
  (x : A) (f : polynomial R) : A :=
monoid_ring.eval _ _ _ (ℕ.UMP A x) f

instance polynomial.eval.is_alg_hom (A : Type v) [comm_ring A] [algebra R A] (r : A) :
  is_alg_hom (polynomial.eval R A r) :=
monoid_ring.eval.is_alg_hom _ _ _ _

def polynomial.UMP (A : Type v) [comm_ring A] [algebra R A] :
  A ≃ alg_hom (polynomial R) A :=
(ℕ.UMP A).trans (monoid_ring.UMP _ _ _)

theorem polynomial.UMP.commute (A : Type v) [comm_ring A] [algebra R A] (x : A) :
  polynomial.UMP R A x (finsupp.single 1 1) = x :=
(polynomial.UMP R A).inverse_apply_apply x

variable {R}

def polynomial.deg (f : polynomial R) : with_zero ℕ :=
f.support.max