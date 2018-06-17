import data.finsupp data.equiv
import .algebra

universes u v w

variables (R : Type u) (M : Type v)
variables [decidable_eq R] [decidable_eq M]
variables [comm_ring R] [add_comm_monoid M]

def monoid_ring : Type (max u v) := M →₀ R

instance monoid_ring.comm_ring : comm_ring (monoid_ring R M) :=
finsupp.to_comm_ring

attribute [instance] add_comm_monoid.to_add_monoid

instance monoid_ring.algebra : algebra R (monoid_ring R M) :=
{ f := λ r, finsupp.single 0 r,
  hom :=
  { map_add := λ x y, finsupp.single_add,
    map_mul := λ x y, by rw [finsupp.single_mul_single, zero_add],
    map_one := rfl } }

class is_add_monoid_monoid_hom {α : Type u} {β : Type v}
  [add_monoid α] [monoid β] (f : α → β) : Prop :=
(add : ∀ a b : α, f (a + b) = f a * f b)
(zero : f 0 = 1)

def monoid_ring.of_monoid (m : M) : monoid_ring R M :=
finsupp.single m 1

instance monoid_ring.of_monoid.is_add_monoid_monoid_hom :
  is_add_monoid_monoid_hom (monoid_ring.of_monoid R M) :=
⟨λ _ _, by dsimp [monoid_ring.of_monoid];
  rw [finsupp.single_mul_single, mul_one],
rfl⟩

def add_monoid_monoid_hom (α : Type u) (β : Type v)
  [add_monoid α] [monoid β] : Type (max u v) :=
subtype $ @is_add_monoid_monoid_hom α β _ _

def monoid_ring.eval (A : Type w) [comm_ring A] [algebra R A]
  (f : add_monoid_monoid_hom M A) (x : monoid_ring R M) : A :=
x.sum $ λ m r, r * f.1 m

instance monoid_ring.eval.is_alg_hom (A : Type w) [comm_ring A] [algebra R A]
  (f : add_monoid_monoid_hom M A) : is_alg_hom (monoid_ring.eval R M A f) :=
have H0 : ∀ m, ↑(0:R) * f.1 m = 0,
  from λ m, by simp,
have Hp : ∀ m (r1 r2 : R), ↑(r1+r2:R) * f.1 m = r1 * f.1 m + r2 * f.1 m,
  from λ m, by simp [add_mul],
{ map_add := λ x y, finsupp.sum_add_index H0 Hp,
  map_mul := begin
      letI : comm_ring (M →₀ R) := monoid_ring.comm_ring R M,
      intros x y,
      unfold monoid_ring.eval,
      apply finsupp.induction x; clear x,
      { simp [finsupp.mul_def, finsupp.sum_zero_index] },
      intros m r x h1 h2 ih,
      rw [add_mul, finsupp.sum_add_index, ih],
      rw [finsupp.sum_add_index, add_mul],
      suffices : finsupp.sum (finsupp.single m r * y) (λ (m : M) (r : R), ↑r * f.val m)
        = ↑r * f.val m * finsupp.sum y (λ (m : M) (r : R), ↑r * f.val m),
      { rw [this, finsupp.sum_single_index], solve_by_elim },
      apply finsupp.induction y; clear ih y,
      { simp [finsupp.mul_def, finsupp.sum_zero_index] },
      intros n s y h3 h4 ih,
      rw [mul_add, finsupp.sum_add_index, ih],
      rw [finsupp.sum_add_index, mul_add],
      rw [finsupp.single_mul_single],
      rw [finsupp.sum_single_index],
      rw [finsupp.sum_single_index],
      rw [f.2.add, algebra.coe_mul],
      ac_refl,
      all_goals { solve_by_elim }
    end,
  map_one := by convert finsupp.sum_single_index _;
    rw [f.2.zero]; simp,
  commute := λ r, by convert finsupp.sum_single_index _;
    rw [f.2.zero]; simp; refl }

def monoid_ring.of_alg_hom (A : Type w) [comm_ring A] [algebra R A]
  (f : alg_hom (monoid_ring R M) A) (x : M) : A :=
f.1 $ finsupp.single x 1

def monoid_ring.UMP (A : Type w) [comm_ring A] [algebra R A] :
  add_monoid_monoid_hom M A ≃ alg_hom (monoid_ring R M) A :=
{ to_fun := λ f, ⟨monoid_ring.eval R M A f, by apply_instance⟩,
  inv_fun := λ f, ⟨λ m, f.1 $ finsupp.single m 1,
    λ x y, by rw [← is_ring_hom.map_mul f.1, finsupp.single_mul_single, mul_one],
    is_ring_hom.map_one f.1⟩,
  left_inv := λ f, subtype.eq $ funext $ λ m,
    by convert finsupp.sum_single_index _; simp; simp,
  right_inv := λ f, subtype.eq $ funext $ λ x,
    begin
      dsimp [monoid_ring.eval],
      apply finsupp.induction x,
      { simp [finsupp.sum_zero_index],
        symmetry, exact is_ring_hom.map_zero f.1 },
      intros m r x h1 h2 ih,
      rw [finsupp.sum_add_index, finsupp.sum_single_index, ih],
      rw [← f.2.commute, ← is_ring_hom.map_mul f.1, is_ring_hom.map_add f.1],
      congr,
      convert finsupp.single_mul_single,
      all_goals { intros, simp [add_mul] }
    end }