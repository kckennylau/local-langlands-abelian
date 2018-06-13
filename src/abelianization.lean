import algebra.group

inductive abelianization.rel (G : Type*) [group G] : G → G → Prop
| basic : ∀ x y z w, abelianization.rel (x * y * z * w) (x * z * y * w)

def abelianization (G : Type*) [group G] : Type* :=
quot (abelianization.rel G)

def abelianization.mul (G : Type*) [group G] :
  abelianization G → abelianization G → abelianization G :=
begin
  refine quot.lift (λ x, quot.lift (λ y, quot.mk (rel G) (x * y)) _) _,
  { intros m n h,
    cases h with m n p q,
    calc  quot.mk (rel G) (x * ((m * n * p) * q))
        = quot.mk (rel G) (x * m * n * p * q) : by simp [mul_assoc]
    ... = quot.mk (rel G) (x * m * p * n * q) : quot.sound ⟨_, _, _, _⟩
    ... = quot.mk (rel G) (x * ((m * p * n) * q)) : by simp [mul_assoc] },
  { intros m n h,
    apply funext,
    apply quot.ind,
    intro x,
    cases h with m n p q,
    calc  quot.mk (rel G) (m * n * p * q * x)
        = quot.mk (rel G) (m * n * p * (q * x)) : by simp [mul_assoc]
    ... = quot.mk (rel G) (m * p * n * (q * x)) : quot.sound ⟨_, _, _, _⟩
    ... = quot.mk (rel G) (m * p * n * q * x) : by simp [mul_assoc] }
end

def abelianization.inv (G : Type*) [group G] :
  abelianization G → abelianization G :=
begin
  refine quot.lift (λ x, quot.mk _ (x⁻¹)) _,
  intros m n h,
  cases h with m n p q,
  calc  quot.mk (rel G) (m * n * p * q)⁻¹
      = quot.mk (rel G) (q⁻¹ * p⁻¹ * n⁻¹ * m⁻¹) : by simp [mul_assoc]
  ... = quot.mk (rel G) (q⁻¹ * n⁻¹ * p⁻¹ * m⁻¹) : quot.sound ⟨_, _, _, _⟩
  ... = quot.mk (rel G) (m * p * n * q)⁻¹ : by simp [mul_assoc]
end

instance abelianization.comm_group (G : Type*) [group G] :
  comm_group (abelianization G) :=
{ mul := abelianization.mul G,
  mul_assoc := by repeat { refine quot.ind (λ x, _) }; simp [abelianization.mul, mul_assoc],
  one := quot.mk _ 1,
  one_mul := by refine quot.ind (λ x, _); simp [abelianization.mul],
  mul_one := by refine quot.ind (λ x, _); simp [abelianization.mul]; congr; apply mul_one,
  inv := abelianization.inv G,
  mul_left_inv := by refine quot.ind (λ x, _); simp [abelianization.mul, abelianization.inv]; refl,
  mul_comm := by refine quot.ind (λ x, _); refine quot.ind (λ y, _); simp [abelianization.mul];
    suffices : quot.mk (rel G) (1 * x * y * 1) = quot.mk (rel G) (1 * y * x * 1);
    [simpa, from quot.sound ⟨_, _, _, _⟩] }

instance abelianization.comm_group' (G : Type*) [group G] :
  comm_group (quot (rel G)) :=
abelianization.comm_group G

instance abelianization.is_group_hom (G : Type*) [group G] :
  is_group_hom (quot.mk (rel G) : G → abelianization G) :=
⟨λ x y, rfl⟩