-- in this construction we do not care about the polynomials
-- we only want its universal mapping property

import data.finsupp data.equiv

class algebra (R : out_param Type*) (A : Type*)
  [out_param $ comm_ring R] extends comm_ring A :=
(f : R → A) [hom : is_ring_hom f]

instance algebra.to_is_ring_hom (R : out_param Type*) (A : Type*)
  [out_param $ comm_ring R] [algebra R A] : is_ring_hom (algebra.f A) :=
algebra.hom A

instance algebra.to_module (R : out_param Type*) (A : Type*)
  [out_param $ comm_ring R] [algebra R A] : module R A :=
{ smul := λ r x, algebra.f A r * x,
  smul_add := λ r x y, mul_add (algebra.f A r) x y,
  add_smul := λ r s x, show algebra.f A (r + s) * x
      = algebra.f A r * x + algebra.f A s * x,
    by rw [is_ring_hom.map_add (algebra.f A), add_mul],
  mul_smul := λ r s x, show algebra.f A (r * s) * x
      = algebra.f A r * (algebra.f A s * x),
    by rw [is_ring_hom.map_mul (algebra.f A), mul_assoc],
  one_smul := λ x, show algebra.f A 1 * x = x,
    by rw [is_ring_hom.map_one (algebra.f A), one_mul] }

theorem algebra.smul_def (R : out_param Type*) (A : Type*)
  [out_param $ comm_ring R] [algebra R A] (c : R) (x : A) :
  c • x = algebra.f A c * x := rfl

class is_alg_hom {R : out_param Type*} {A : Type*} {B : Type*}
  [out_param $ comm_ring R] [algebra R A] [algebra R B]
  (φ : A → B) extends is_ring_hom φ : Prop :=
(commute : ∀ r, φ (algebra.f A r) = algebra.f B r)

def alg_hom {R : out_param Type*} (A : Type*) (B : Type*)
  [out_param $ comm_ring R] [algebra R A] [algebra R B] :=
{ φ : A → B // is_alg_hom φ }

instance alg_hom.to_is_alg_hom {R : out_param Type*} (A : Type*) (B : Type*)
  [out_param $ comm_ring R] [algebra R A] [algebra R B]
  (φ : alg_hom A B) : is_alg_hom φ.val :=
φ.property

instance alg_hom.to_is_ring_hom {R : out_param Type*} (A : Type*) (B : Type*)
  [out_param $ comm_ring R] [algebra R A] [algebra R B]
  (φ : alg_hom A B) : is_ring_hom φ.val :=
by apply_instance

instance alg_hom.has_coe_to_fun {R : out_param Type*} (A : Type*) (B : Type*)
  [out_param $ comm_ring R] [algebra R A] [algebra R B] :
  has_coe_to_fun (alg_hom A B) :=
⟨_, λ φ, φ.1⟩

instance comm_ring.to_algebra (R : Type*) [comm_ring R] : algebra R R :=
{ f := id }

variables (R : Type*) [decidable_eq R] [comm_ring R]

def polynomial : Type* := ℕ →₀ R

instance polynomial.comm_ring : comm_ring (polynomial R) :=
finsupp.to_comm_ring

instance polynomial.algebra : algebra R (polynomial R) :=
{ f := λ r, finsupp.single 0 r,
  hom :=
  { map_add := λ x y, finsupp.single_add,
    map_mul := λ x y, show finsupp.single (0 + 0) (x * y) = _, from finsupp.single_mul_single.symm,
    map_one := rfl } }

def polynomial.eval (A : Type*) [algebra R A] (x : A) : polynomial R → A :=
λ f, f.sum $ λ n c, c • x^n

instance polynomial.eval.is_alg_hom (A : Type*) [algebra R A] (r : A) :
  is_alg_hom (polynomial.eval R A r) :=
have H1 : ∀ n c, finsupp.sum (finsupp.single n c) (λ (n : ℕ) (c : R), c • r ^ n) = c • r ^ n,
  from λ n c, finsupp.sum_single_index zero_smul,
have Hp : ∀ f g : polynomial R, finsupp.sum (f + g) (λ (n : ℕ) (c : R), c • r ^ n) =
      finsupp.sum f (λ (n : ℕ) (c : R), c • r ^ n)
    + finsupp.sum g (λ (n : ℕ) (c : R), c • r ^ n),
  from λ f g, finsupp.sum_add_index (λ _, zero_smul) (λ _ _ _, add_smul),
{ map_add := Hp,
  map_mul :=
  begin
    intros f g,
    change finsupp.sum (f * g) (λ (n : ℕ) (c : R), c • r ^ n) =
      finsupp.sum f (λ (n : ℕ) (c : R), c • r ^ n) * finsupp.sum g (λ (n : ℕ) (c : R), c • r ^ n),
    rw [finsupp.mul_def, finsupp.sum_sum_index],
    apply finsupp.induction f,
    { simp [finsupp.sum_zero_index] },
    { intros n c f hf hc ih,
      rw [finsupp.sum_add_index, finsupp.sum_single_index, ih],
      rw [Hp, H1, add_mul],
      suffices : finsupp.sum (finsupp.sum g (λ (a₂ : ℕ) (b₂ : R), finsupp.single (n + a₂) (c * b₂)))
        (λ (n : ℕ) (c : R), c • r ^ n)
        = c • r ^ n * finsupp.sum g (λ (n : ℕ) (c : R), c • r ^ n),
      { rw this },
      apply finsupp.induction g,
      { simp [finsupp.sum_zero_index] },
      { intros n c g hg hc ih,
        rw [finsupp.sum_add_index, finsupp.sum_single_index],
        rw [Hp, H1, ih, Hp, H1],
        rw [mul_add, mul_smul, pow_add],
        rw [algebra.smul_def, algebra.smul_def, algebra.smul_def, algebra.smul_def],
        ac_refl,
        { rw [mul_zero, finsupp.single_zero] },
        { intros, rw [mul_zero, finsupp.single_zero] },
        { intros,
          rw [mul_add, finsupp.single_add] } },
      { convert finsupp.sum_zero_index,
        convert finsupp.sum_zero,
        funext,
        rw [zero_mul, finsupp.single_zero],
        apply_instance, apply_instance },
      { intros,
        convert finsupp.sum_zero_index,
        convert finsupp.sum_zero,
        funext,
        rw [zero_mul, finsupp.single_zero],
        apply_instance, apply_instance },
      { intros a r s,
        apply finsupp.induction g,
        { simp [finsupp.sum_zero_index] },
        { intros n c g hg hc ih,
          convert Hp _ _,
          convert finsupp.sum_add,
          { funext, rw [add_mul, finsupp.single_add] },
          apply_instance, apply_instance } } },
      { intros, apply zero_smul },
      { intros, apply add_smul }
  end,
  map_one := by convert H1 0 1; rw [one_smul]; refl,
  commute := λ r, by unfold algebra.f; unfold polynomial.eval;
    rw [finsupp.sum_single_index];
    [apply mul_one, { change (0:R) • (1:A) = 0, apply zero_smul }]}

def polynomial.UMP (A : Type*) [algebra R A] :
  A ≃ alg_hom (polynomial R) A :=
{ to_fun := λ r, ⟨polynomial.eval R A r, by apply_instance⟩,
  inv_fun := λ φ, φ.1 (finsupp.single 1 1),
  left_inv := λ r, by dsimp [polynomial.eval]; rw [finsupp.sum_single_index];
    [{ change (1:R) • (r^1:A) = r, rw [one_smul, pow_one] },
     { change (0:R) • (r^1:A) = 0, apply zero_smul }],
  right_inv := λ φ, subtype.eq $ funext $ λ f,
    begin
      dsimp [polynomial.eval],
      apply finsupp.induction f,
      { rw [finsupp.sum_zero_index];
        from (is_ring_hom.map_zero φ.1).symm },
      intros n c f hf hc ih,
      dsimp,
      rw [finsupp.sum_add_index, finsupp.sum_single_index],
      rw [is_ring_hom.map_add φ.1, ← ih, algebra.smul_def],
      rw [← is_alg_hom.commute φ.1],
      unfold algebra.f,
      suffices : φ.val (finsupp.single 0 c) * φ.val (finsupp.single 1 1) ^ n = φ.val (finsupp.single n c),
      { simp [-add_comm], exact this },
      apply nat.rec_on n,
      { rw [pow_zero, mul_one] },
      { intros n ih,
        rw [pow_succ, mul_left_comm, ih],
        rw [← is_ring_hom.map_mul φ.1, finsupp.single_mul_single],
        rw [nat.one_add, one_mul] },
      { apply zero_smul },
      { intros, apply zero_smul},
      { intros, apply add_smul }
    end }

theorem polynomial.UMP.commute (A : Type*) [algebra R A] (x : A) :
  polynomial.UMP R A x (finsupp.single 1 1) = x :=
(polynomial.UMP R A).inverse_apply_apply x

variable {R}

def polynomial.deg (f : polynomial R) : with_zero ℕ :=
f.support.max