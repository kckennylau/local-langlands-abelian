import data.finsupp data.equiv.basic
import .algebra

universes u v w

class is_add_monoid_monoid_hom {α : Type u} {β : Type v}
  [add_monoid α] [monoid β] (f : α → β) : Prop :=
(add : ∀ a b : α, f (a + b) = f a * f b)
(zero : f 0 = 1)

def add_monoid_monoid_hom (α : Type u) (β : Type v)
  [add_monoid α] [monoid β] : Type (max u v) :=
subtype $ @is_add_monoid_monoid_hom α β _ _

instance add_monoid_monoid_hom.is_add_monoid_monoid_hom (α : Type u) (β : Type v)
  [add_monoid α] [monoid β] (f : add_monoid_monoid_hom α β) :
  is_add_monoid_monoid_hom f.1 := f.2

variables (R : Type u) (M : Type v)
variables [decidable_eq R] [decidable_eq M]
variables [comm_ring R] [add_comm_monoid M]

def monoid_ring : Type (max u v) := M →₀ R

namespace monoid_ring

instance : comm_ring (monoid_ring R M) := finsupp.to_comm_ring
instance : module R (monoid_ring R M) := finsupp.to_module _ _
instance : has_scalar R (monoid_ring R M) := infer_instance

protected def algebra : algebra R (monoid_ring R M) :=
{ to_fun := λ r, finsupp.single 0 r,
  hom :=
  { map_add := λ x y, finsupp.single_add,
    map_mul := λ x y, by rw [finsupp.single_mul_single, zero_add],
    map_one := rfl },
  smul_def' := begin
    intros r x, ext m,
    rw [finsupp.smul_apply, finsupp.mul_def, finsupp.sum_apply, finsupp.sum_single_index,
        finsupp.sum_apply, finsupp.sum, finset.sum_eq_single m _ _, zero_add, finsupp.single_eq_same, smul_eq_mul],
    { intros b _ hbm, rw [zero_add, finsupp.single_eq_of_ne hbm] },
    { intros hmx, rw [zero_add, finsupp.single_eq_same, finsupp.not_mem_support_iff.1 hmx, mul_zero] },
    { rw finsupp.sum_apply, refine eq.trans (finset.sum_congr rfl $ λ m hmx, _) finsupp.sum_zero,
      dsimp only, rw [zero_mul, finsupp.single_zero, finsupp.zero_apply] }
  end }

def of_monoid (m : M) : monoid_ring R M :=
finsupp.single m 1

instance : is_add_monoid_monoid_hom (monoid_ring.of_monoid R M) :=
⟨λ m₁ m₂, by unfold of_monoid; rw [finsupp.single_mul_single, mul_one], rfl⟩

theorem of_monoid_add (m₁ m₂ : M) : of_monoid R M (m₁ + m₂) = of_monoid R M m₁ * of_monoid R M m₂ :=
is_add_monoid_monoid_hom.add _ _ _

theorem of_monoid_zero : of_monoid R M 0 = 1 :=
is_add_monoid_monoid_hom.zero _

variables {R M}
@[elab_as_eliminator]
protected theorem induction_on {C : monoid_ring R M → Prop} (z)
  (H0 : ∀ m, C (of_monoid R M m)) (H1 : ∀ x y, C x → C y → C (x + y))
  (H2 : ∀ (r : R) x, C x → C (r • x)) : C z :=
finsupp.induction z (@zero_smul R _ _ _ _ (1 : monoid_ring R M) ▸ H2 0 1 (H0 0)) $ λ m r z _ _ ih,
have r • of_monoid R M m = finsupp.single m r, by conv_rhs { rw [← mul_one r, ← smul_eq_mul, ← finsupp.smul_single] }; refl,
H1 (finsupp.single m r) z (this ▸ H2 r (of_monoid R M m) (H0 m)) ih
variables (R M)

variables {A : Type w} [comm_ring A] [decidable_eq A] (i : algebra R A)

set_option class.instance_max_depth 100
def eval (f : M → i.mod) (hf : is_add_monoid_monoid_hom f) : monoid_ring.algebra R M →ₐ i :=
{ to_fun := λ x, x.sum $ λ m r, (r • f m : i.mod),
  hom := ⟨by refine (finsupp.sum_single_index _).trans _;
      simp only [i.smul_def, i.map_zero, i.map_one, is_add_monoid_monoid_hom.zero f]; apply mul_one,
    begin
      intros x y,
      rw [finsupp.mul_def, finsupp.sum_sum_index, finsupp.sum_mul],
      refine finset.sum_congr rfl (λ m₁ _, _), dsimp only,
      rw [finsupp.sum_sum_index, finsupp.mul_sum],
      refine finset.sum_congr rfl (λ m₂ _, _), dsimp only,
      rw [finsupp.sum_single_index, is_add_monoid_monoid_hom.add f,
        algebra.smul_mul, algebra.mul_smul, smul_smul],
      all_goals { intros, apply zero_smul <|> apply add_smul }
    end,
    have H0 : ∀ m, (0 • f m : i.mod) = 0,
      from λ _, zero_smul _,
    have Hp : ∀ m (r1 r2 : R), ((r1 + r2) • f m : i.mod) = r1 • f m + r2 • f m,
      from λ _ _ _, add_smul _ _ _,
    λ x y, finsupp.sum_add_index H0 Hp⟩,
  commutes' := λ r, by refine (finsupp.sum_single_index _).trans _;
    simp only [i.smul_def, i.map_zero, i.map_one, is_add_monoid_monoid_hom.zero f]; apply mul_one }

theorem eval_of_monoid (f : M → i.mod) (hf) (m) : eval R M i f hf (of_monoid R M m) = f m :=
by convert finsupp.sum_single_index _; [exact (one_smul _).symm, exact (zero_smul _)]

theorem eq_eval (φ : monoid_ring.algebra R M →ₐ i) : φ = eval R M i (λ m, φ (of_monoid R M m))
  ⟨λ m₁ m₂, by rw [of_monoid_add, φ.map_mul], φ.map_one⟩ :=
begin
  ext x,
  refine monoid_ring.induction_on x (λ m, _) (λ x y ihx ihy, _) (λ r x ih, _),
  { rw eval_of_monoid },
  { change _ at ihx, change _ at ihy,
    rw [φ.map_add, alg_hom.map_add, ihx, ihy] },
  { change _ at ih,
    rw [(monoid_ring.algebra R M).smul_def, φ.map_mul, alg_hom.map_mul, φ.commutes, alg_hom.commutes, ih] }
end

protected theorem ext (φ₁ φ₂ : monoid_ring.algebra R M →ₐ i)
  (H : ∀ m, φ₁ (of_monoid R M m) = φ₂ (of_monoid R M m)) : φ₁ = φ₂ :=
by rw [eq_eval _ _ _ φ₁, eq_eval _ _ _ φ₂]; congr' 1; ext m; apply H

protected def monoid_ring.UMP :
  add_monoid_monoid_hom M A ≃ alg_hom (monoid_ring.algebra R M) i :=
{ to_fun := λ f, monoid_ring.eval R M i f.1 f.2,
  inv_fun := λ f, ⟨λ m, f (of_monoid R M m),
    λ m₁ m₂, by rw [of_monoid_add, f.map_mul], f.map_one⟩,
  left_inv := λ f, subtype.eq $ funext $ eval_of_monoid _ _ _ _ f.2,
  right_inv := λ f, (eq_eval _ _ _ _).symm }

end monoid_ring