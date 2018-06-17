import .tensor_product .algebra
noncomputable theory

set_option eqn_compiler.zeta true

universes u v w u₁ v₁ w₁

variables (R : Type u) [comm_ring R]
variables (A : Type v) [comm_ring A] [algebra R A]
variables (B : Type w) [comm_ring B] [algebra R B]

@[reducible] def tensor_a : Type (max v w) :=
@tensor_product R A B _ _ _

instance tensor_a.module : module R (tensor_a R A B) :=
tensor_product.module R A B

open tensor_product
open tensor_product.universal_property

def tensor_a.mul : tensor_a R A B → tensor_a R A B → tensor_a R A B :=
let h1 : A → B → A → B → tensor_a R A B :=
  λ r s p q, (p * r) ⊗ₛ (q * s) in
have h2 : ∀ r s, is_bilinear_map (h1 r s),
  from λ r s, by apply is_bilinear_map.mk;
    intros; simp [h1];
    [rw [add_mul, add_tprod], rw [add_mul, tprod_add],
    rw [← smul_tprod, algebra.smul_def, algebra.smul_def, mul_assoc],
    rw [← tprod_smul, algebra.smul_def, algebra.smul_def, mul_assoc]],
have h3 : ∀ r s, is_bilinear_map (λ p q, h1 p q r s),
  from λ r s, by apply is_bilinear_map.mk;
    intros; simp [h1];
    [rw [mul_add, add_tprod], rw [mul_add, tprod_add],
    rw [← smul_tprod, algebra.smul_def, algebra.smul_def, mul_left_comm],
    rw [← tprod_smul, algebra.smul_def, algebra.smul_def, mul_left_comm]],
let h4 : tensor_a R A B → A → B → tensor_a R A B :=
  λ x r s, factor (h2 r s) x in
have h5 : ∀ x, is_bilinear_map (h4 x), from λ x,
  by apply is_bilinear_map.mk; intros; refine tensor_product.ext x _ _ _;
  try { apply_instance <|> apply is_linear_map.map_add
    <|> apply is_linear_map.map_smul_right
    <|> apply is_linear_map.map_smul_left };
  try { apply factor_linear };
  intros c d; dsimp [h4]; simp [factor_commutes];
  cases h3 c d; solve_by_elim,
λ x, factor (h5 x)

theorem tensor_a.mul.is_linear_map (x) :
  is_linear_map (tensor_a.mul R A B x) :=
by simp [tensor_a.mul]; apply factor_linear

theorem tensor_a.mul.is_bilinear_map :
  is_bilinear_map (tensor_a.mul R A B) :=
{ add_pair := λ x y z, by simp [tensor_a.mul]; refine tensor_product.ext z _ _ _;
    try { apply_instance <|> apply is_linear_map.map_add };
    try { apply factor_linear };
    intros; rw [factor_commutes, factor_commutes, factor_commutes];
    rw [(factor_linear _).add],
  pair_add := λ x, (tensor_a.mul.is_linear_map R A B x).add,
  smul_pair := λ c x y, by simp [tensor_a.mul]; refine tensor_product.ext y _ _ _;
    try { apply_instance <|> apply is_linear_map.map_smul_right };
    try { apply factor_linear };
    intros; rw [factor_commutes, factor_commutes];
    rw [(factor_linear _).smul],
  pair_smul := λ c x, (tensor_a.mul.is_linear_map R A B x).smul c, }

instance tensor_a.comm_ring : comm_ring (tensor_a R A B) :=
{ mul := tensor_a.mul R A B,
  mul_assoc := λ x y z, tensor_product.ext z (factor_linear _)
    (((tensor_a.mul.is_bilinear_map R A B).pair_linear x).comp
        ((tensor_a.mul.is_bilinear_map R A B).pair_linear y)) $
    λ c d, by simp [tensor_a.mul, factor_commutes]; apply tensor_product.ext y
      ((factor_linear _).comp (factor_linear _))
      ((factor_linear _).comp (factor_linear _)) _; from
    λ e f, by simp [factor_commutes]; apply tensor_product.ext x
      ((factor_linear _).comp (factor_linear _)) (factor_linear _) _; from
    λ g h, by simp [factor_commutes, mul_assoc],
  one := 1 ⊗ₛ 1,
  one_mul := λ x, tensor_product.ext x (tensor_a.mul.is_linear_map _ _ _ _)
    is_linear_map.id (λ _ _, by simp [tensor_a.mul, factor_commutes]),
  mul_one := λ x, tensor_product.ext x
    ((tensor_a.mul.is_bilinear_map _ _ _).linear_pair (1 ⊗ₛ 1))
    is_linear_map.id (λ _ _, by simp [tensor_a.mul, factor_commutes]),
  left_distrib := (tensor_a.mul.is_bilinear_map R A B).pair_add,
  right_distrib := (tensor_a.mul.is_bilinear_map R A B).add_pair,
  mul_comm := λ x y, tensor_product.ext y (tensor_a.mul.is_linear_map _ _ _ _)
      ((tensor_a.mul.is_bilinear_map _ _ _).linear_pair _) $
    λ c d, tensor_product.ext x
      ((tensor_a.mul.is_bilinear_map _ _ _).linear_pair _)
      (tensor_a.mul.is_linear_map _ _ _ _) $
    λ e f, show tensor_a.mul R A B (e ⊗ₛ f) (c ⊗ₛ d) = tensor_a.mul R A B (c ⊗ₛ d) (e ⊗ₛ f),
    by simp [tensor_a.mul, factor_commutes, mul_comm],
  .. tensor_product.module R A B }

instance tensor_a.comm_ring' : comm_ring (tensor_product A B) :=
tensor_a.comm_ring R A B

theorem tensor_a.mul_def' (p : A) (q : B) (r : A) (s : B) :
  tensor_a.mul R A B (p ⊗ₛ q) (r ⊗ₛ s) = (p * r) ⊗ₛ (q * s) :=
by simp [tensor_a.mul, factor_commutes]

theorem tensor_a.mul_def (p : A) (q : B) (r : A) (s : B) :
  (p ⊗ₛ q : tensor_a R A B) * (r ⊗ₛ s) = (p * r) ⊗ₛ (q * s) :=
tensor_a.mul_def' R A B p q r s

theorem tensor_a.one_def : (1 : tensor_a R A B) = 1 ⊗ₛ 1 := rfl

theorem tensor_a.smul_def_left (r : R) (p : A) (q : B) :
  r • (p ⊗ₛ q : tensor_a R A B) = (r * p) ⊗ₛ q :=
by rw [← algebra.smul_def, smul_tprod]

theorem tensor_a.smul_def_right (r : R) (p : A) (q : B) :
  r • (p ⊗ₛ q : tensor_a R A B) = p ⊗ₛ (r * q) :=
by rw [← algebra.smul_def, tprod_smul]

instance tensor_a.algebra : algebra R (tensor_a R A B) :=
{ f := λ r, r ⊗ₛ 1,
  hom := ⟨λ _ _, by simp [add_tprod],
    λ _ _, by simp [tensor_a.mul_def],
    by simp; refl⟩ }

theorem tensor_a.coe_def (r : R) : (r : tensor_a R A B) = r ⊗ₛ 1 := rfl
theorem tensor_a.coe_def' (r : R) : (r : tensor_a R A B) = 1 ⊗ₛ r :=
suffices ((r * 1) ⊗ₛ 1 : tensor_a R A B) = 1 ⊗ₛ (r * 1),
  by simpa using this,
by rw [← algebra.smul_def, ← algebra.smul_def, tprod_smul, smul_tprod]

theorem tensor_a.smul_def (r : R) (x : tensor_a R A B) :
  @has_scalar.smul _ _ (tensor_a.module R A B).to_has_scalar r x
  = @has_scalar.smul _ _ (algebra.to_module _ _).to_has_scalar r x :=
tensor_product.ext x (is_linear_map.map_smul_right is_linear_map.id)
  (tensor_a.mul.is_linear_map _ _ _ _) $ λ x y,
by simp [tensor_a.smul_def_left, algebra.smul_def, tensor_a.coe_def, tensor_a.mul_def]

@[simp, reducible] def tensor_a.inl (x : A) : tensor_a R A B := x ⊗ₛ 1
@[simp, reducible] def tensor_a.inr (y : B) : tensor_a R A B := 1 ⊗ₛ y

instance tensor_a.inl.is_alg_hom : is_alg_hom (tensor_a.inl R A B) :=
{ map_add := λ _ _, add_tprod,
  map_mul := λ _ _, by simp [tensor_a.mul_def],
  map_one := rfl,
  commute := λ _, rfl }

instance tensor_a.inr.is_alg_hom : is_alg_hom (tensor_a.inr R A B) :=
{ map_add := λ _ _, tprod_add,
  map_mul := λ _ _, by simp [tensor_a.mul_def],
  map_one := rfl,
  commute := λ r, (tensor_a.coe_def' R A B r).symm }

@[simp] def alg_hom.inl : alg_hom A (tensor_a R A B) :=
⟨tensor_a.inl R A B, tensor_a.inl.is_alg_hom R A B⟩

@[simp] def alg_hom.inr : alg_hom B (tensor_a R A B) :=
⟨tensor_a.inr R A B, tensor_a.inr.is_alg_hom R A B⟩

def tensor_a.to (C : Type u₁) [comm_ring C] [algebra R C]
  (f : alg_hom A C) (g : alg_hom B C) (x : tensor_a R A B) : C :=
let h1 : A → B → C := λ x y, f.1 x * g.1 y in
have h2 : is_bilinear_map h1,
  by constructor; intros; simp [h1, algebra.smul_def];
    [rw [f.2.1.1, add_mul], rw [g.2.1.1, mul_add],
    rw [f.2.1.2, f.2.2, mul_assoc],
    rw [g.2.1.2, g.2.2, mul_left_comm]],
factor h2 x

instance tensor_a.to.is_alg_hom (C : Type u₁) [comm_ring C] [algebra R C]
  (f : alg_hom A C) (g : alg_hom B C) : is_alg_hom (tensor_a.to R A B C f g) :=
{ map_add := λ x y, by simp [tensor_a.to, (factor_linear _).add],
  map_mul := λ x y, by simp [tensor_a.to]; apply tensor_product.ext y
      ((factor_linear _).comp (tensor_a.mul.is_linear_map R A B x))
      ((is_linear_map.mul_left _ _ _).comp (factor_linear _)) _; from
    λ p q, by simp; apply tensor_product.ext x
      ((factor_linear _).comp ((tensor_a.mul.is_bilinear_map R A B).linear_pair _))
      ((is_linear_map.mul_right _ _ _).comp (factor_linear _)) _; from
    λ r s, by simp [factor_commutes, tensor_a.mul_def', f.2.1.2, g.2.1.2]; ac_refl,
  map_one := by simp [tensor_a.to, tensor_a.one_def, factor_commutes, f.2.1.3, g.2.1.3],
  commute := λ r, by simp [tensor_a.to, tensor_a.coe_def, factor_commutes, f.2.2, g.2.1.3] }

def tensor_a.UMP (C : Type u₁) [comm_ring C] [algebra R C] :
  (alg_hom A C × alg_hom B C) ≃ alg_hom (tensor_a R A B) C :=
{ to_fun := λ f, ⟨tensor_a.to R A B C f.1 f.2, by apply_instance⟩,
  inv_fun := λ f, (⟨f.1 ∘ tensor_a.inl R A B, is_alg_hom.comp _ _⟩,
    ⟨f.1 ∘ tensor_a.inr R A B, is_alg_hom.comp _ _⟩),
  left_inv := λ ⟨f, g⟩, prod.ext.2
    ⟨subtype.eq $ funext $ λ x, by simp [tensor_a.to, tensor_a.inl, factor_commutes, g.2.1.3],
    subtype.eq $ funext $ λ x, by simp [tensor_a.to, tensor_a.inl, factor_commutes, f.2.1.3]⟩,
  right_inv := λ f, subtype.eq $ funext $ λ x, tensor_product.ext x
      (is_linear_map.mk (λ _ _, by simp [tensor_a.to, (factor_linear _).add])
        (λ _ _, by simp [tensor_a.to, (factor_linear _).smul]))
      (is_linear_map.mk f.2.1.1 $ λ c x,
        by simp [tensor_a.smul_def, algebra.smul_def, f.2.1.2, f.2.2]) $
    λ c d, by simp [tensor_a.to, factor_commutes, tensor_a.inl, tensor_a.inr];
      rw [← f.2.1.2, tensor_a.mul_def, mul_one, one_mul] }

@[simp] lemma tensor_a.to.val (C : Type u₁) [comm_ring C] [algebra R C]
  (f : alg_hom A C) (g : alg_hom B C) (x : A) (y : B) :
  (tensor_a.to R A B C f g) (x ⊗ₛ y) = f.1 x * g.1 y :=
by simp [tensor_a.to, factor_commutes]

@[simp] lemma tensor_a.UMP.to_fun.val (C : Type u₁) [comm_ring C] [algebra R C]
  (f : alg_hom A C) (g : alg_hom B C) (x : A) (y : B) :
  ((tensor_a.UMP R A B C).1 (f, g)).1 (x ⊗ₛ y) = f.1 x * g.1 y :=
by simp [tensor_a.UMP]

def tensor_a.map (C : Type v₁) (D : Type w₁)
  [comm_ring C] [algebra R C] [comm_ring D] [algebra R D]
  (f : alg_hom A C) (g : alg_hom B D) :
  alg_hom (tensor_a R A B) (tensor_a R C D) :=
(tensor_a.UMP R A B (tensor_a R C D)).1
  ((alg_hom.inl R C D).comp f, (alg_hom.inr R C D).comp g)

@[simp] lemma tensor_a.map.val (C : Type v₁) (D : Type w₁)
  [comm_ring C] [algebra R C] [comm_ring D] [algebra R D]
  (f : alg_hom A C) (g : alg_hom B D) (x : A) (y : B) :
  (tensor_a.map R A B C D f g).1 (x ⊗ₛ y) = f.1 x ⊗ₛ g.1 y :=
by simp [tensor_a.map, alg_hom.inl, alg_hom.inr,
  tensor_a.inl, tensor_a.inr, tensor_a.mul_def]

def alg_hom.tensor_assoc (C : Type u₁) [comm_ring C] [algebra R C] :
  alg_hom (tensor_a R (tensor_a R A B) C) (tensor_a R A (tensor_a R B C)) :=
(tensor_a.UMP R _ _ _).1
  ((tensor_a.UMP R _ _ _).1
    (alg_hom.inl R _ _,
    (alg_hom.inr R _ _).comp (alg_hom.inl R _ _)),
  (alg_hom.inr R _ _).comp (alg_hom.inr R _ _))

@[simp] lemma alg_hom.tensor_assoc.val (C : Type u₁) [comm_ring C] [algebra R C]
  (x : A) (y : B) (z : C) : (alg_hom.tensor_assoc R A B C).1
    (@tprod _ _ _ _ (algebra.to_module R (tensor_a R A B)) _ (x ⊗ₛ y) z)
  = @tprod _ _ _ _ _ (algebra.to_module R (tensor_a R B C)) x (y ⊗ₛ z) :=
by simp [alg_hom.tensor_assoc, tensor_a.mul_def]

def alg_hom.tensor_assoc' (C : Type u₁) [comm_ring C] [algebra R C] :
  alg_hom (tensor_a R A (tensor_a R B C)) (tensor_a R (tensor_a R A B) C) :=
(tensor_a.UMP R _ _ _).1
  ((alg_hom.inl R _ _).comp (alg_hom.inl R _ _),
  (tensor_a.UMP R _ _ _).1
    ((alg_hom.inl R _ _).comp (alg_hom.inr R _ _),
    alg_hom.inr R _ _))

local attribute [instance] comm_ring.to_algebra

@[simp] def alg_hom.ring_tensor : @alg_hom R (tensor_a R R A) A _ _ _ _ _ :=
(tensor_a.UMP R _ _ _).1 (alg_hom.f A, alg_hom.id A)

@[simp] def alg_hom.tensor_ring : @alg_hom R (tensor_a R A R) A _ _ _ _ _ :=
(tensor_a.UMP R _ _ _).1 (alg_hom.id A, alg_hom.f A)