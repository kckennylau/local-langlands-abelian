import .algebra
noncomputable theory

set_option eqn_compiler.zeta true

universes u v w u₁ v₁ w₁

infix ` ⊗ `:100 := tensor_product

variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}
variables [comm_ring R] [comm_ring A] [comm_ring B] [comm_ring C] [comm_ring D]
variables (iA : algebra R A) (iB : algebra R B) (iC : algebra R C) (iD : algebra R D)

namespace tensor_product
open linear_map

set_option class.instance_max_depth 200
def lmul : iA.mod ⊗ iB.mod →ₗ iA.mod ⊗ iB.mod →ₗ iA.mod ⊗ iB.mod :=
lift $ linear_map.compr₂
  ((linear_map.lflip _ _ _ _).comp $
    linear_map.compr₂
      (curry $ curry $ map (lift iA.lmul) $
        lift iB.lmul)
      (lcurry _ _ _))
  (uncurry _ _ _)

theorem lmul_tmul (p : iA.mod) (q : iB.mod) (r : iA.mod) (s : iB.mod) :
  lmul iA iB (p ⊗ₜ q) (r ⊗ₜ s) = (p * r) ⊗ₜ (q * s) :=
by rw [lmul, lift.tmul, compr₂_apply, uncurry_apply, comp_apply, lflip_apply, compr₂_apply, lcurry_apply,
    curry_apply, curry_apply, map_tmul, lift.tmul, lift.tmul]; refl

instance : comm_ring (iA.mod ⊗ iB.mod) :=
{ mul := λ x y, lmul iA iB x y,
  mul_assoc := begin
    intros x y z,
    show lmul iA iB (lmul iA iB x y) z =
      lmul iA iB x (lmul iA iB y z),
    refine tensor_product.induction_on _ _ z _ (λ z₁ z₂, _) (λ z₁ z₂ ih₁ ih₂, _),
    { simp only [map_zero] },
    { refine tensor_product.induction_on _ _ y _ (λ y₁ y₂, _) (λ y₁ y₂ ih₁ ih₂, _),
      { rw [map_zero₂, map_zero, map_zero₂] },
      { refine tensor_product.induction_on _ _ x _ (λ x₁ x₂, _) (λ x₁ x₂ ih₁ ih₂, _),
        { rw [map_zero₂, map_zero₂, map_zero₂] },
        { iterate 4 { rw [lmul_tmul] },
          iterate 2 { rw mul_assoc } },
        { rw [map_add₂, map_add₂, map_add₂], congr' 1, exacts [ih₁, ih₂] } },
      { rw [map_add₂, map_add, map_add₂, map_add], congr' 1, exacts [ih₁, ih₂] } },
    { rw [map_add, map_add, map_add], congr' 1, exacts [ih₁, ih₂] }
  end,
  one := 1 ⊗ₜ 1,
  one_mul := λ x, show lmul iA iB (1 ⊗ₜ 1) x = x, from
    tensor_product.induction_on _ _ x (map_zero _)
    (λ x y, (lmul_tmul _ _ _ _ _ _).trans $ by rw [one_mul, one_mul])
    (λ x y ihx ihy, (map_add _ _ _).trans $ by rw [ihx, ihy]),
  mul_one := λ x, show lmul iA iB x (1 ⊗ₜ 1) = x, from
    tensor_product.induction_on _ _ x (map_zero₂ _ _)
    (λ x y, (lmul_tmul _ _ _ _ _ _).trans $ by rw [mul_one, mul_one])
    (λ x y ihx ihy, (map_add₂ _ _ _ _).trans $ by rw [ihx, ihy]),
  left_distrib := λ _, map_add _,
  right_distrib := map_add₂ _,
  mul_comm := λ x y, show lmul iA iB x y = lmul iA iB y x, from
    tensor_product.induction_on _ _ x (by rw [map_zero₂, map_zero])
      (λ x₁ x₂, tensor_product.induction_on _ _ y (by rw [map_zero₂, map_zero])
        (λ y₁ y₂, by rw [lmul_tmul, lmul_tmul, mul_comm x₁ y₁, mul_comm x₂ y₂])
        (λ y₁ y₂ ih₁ ih₂, by rw [map_add₂, map_add, ih₁, ih₂]))
      (λ x₁ x₂ ih₁ ih₂, by rw [map_add₂, map_add, ih₁, ih₂]),
  .. tensor_product.add_comm_group _ _ }

set_option class.instance_max_depth 32

theorem mul_def (p : iA.mod) (q : iB.mod) (r : iA.mod) (s : iB.mod) :
  (p ⊗ₜ q) * (r ⊗ₜ s) = (p * r) ⊗ₜ (q * s) :=
lmul_tmul _ _ _ _ _ _

theorem one_def : (1 : iA.mod ⊗ iB.mod) = 1 ⊗ₜ 1 := rfl

end tensor_product

namespace algebra
open tensor_product linear_map

def tensor_product : algebra R (iA.mod ⊗ iB.mod) :=
{ to_fun := λ r, iA r ⊗ₜ 1,
  hom := ⟨by rw iA.map_one; refl,
    λ x y, by rw [iA.map_mul, mul_def, mul_one],
    λ x y, by rw [iA.map_add, add_tmul]⟩,
  smul_def' := λ r x, tensor_product.induction_on _ _ x
    (by rw [smul_zero, mul_zero])
    (λ x y, by rw [← tmul_smul, ← smul_tmul, mul_def, iA.smul_def, one_mul])
    (λ x y ihx ihy, by rw [smul_add, mul_add, ihx, ihy]) }

def inl : iA →ₐ iA.tensor_product iB :=
{ to_fun := λ x, x ⊗ₜ 1,
  hom := ⟨rfl, λ x y, by rw [mul_def, mul_one], λ x y, add_tmul _ _ _⟩,
  commutes' := λ r, rfl }

theorem inl_def (p : iA.mod) : iA.inl iB p = p ⊗ₜ 1 := rfl

def inr : iB →ₐ iA.tensor_product iB :=
{ to_fun := λ x, 1 ⊗ₜ x,
  hom := ⟨rfl, λ x y, by rw [mul_def, mul_one], λ x y, tmul_add _ _ _⟩,
  commutes' := λ r, by rw [← mul_one (iB r), ← iB.smul_def, ← smul_tmul, iA.smul_def, mul_one]; refl }

theorem inr_def (q : iB.mod) : iA.inr iB q = 1 ⊗ₜ q := rfl

namespace tensor_product

variables {iA iB iC}
set_option class.instance_max_depth 100
@[elab_with_expected_type]
def arec (f : iA →ₐ iC) (g : iB →ₐ iC) : iA.tensor_product iB →ₐ iC :=
{ to_fun := (tensor_product.lift iC.lmul).comp $ map f.to_linear_map g.to_linear_map,
  hom := ⟨by rw [one_def, comp_apply, map_tmul, lift.tmul]; show f 1 * g 1 = 1;
      rw [f.map_one, g.map_one, mul_one],
    λ x y, tensor_product.induction_on _ _ x
      (by rw [zero_mul, linear_map.map_zero]; exact (zero_mul _).symm)
      (λ x₁ x₂, tensor_product.induction_on _ _ y
        (by rw [mul_zero, linear_map.map_zero]; exact (mul_zero _).symm)
        (λ y₁ y₂, by simp only [mul_def, comp_apply, map_tmul, lift.tmul];
          change f _ * g _ = (f _ * g _) * (f _ * g _);
          rw [f.map_mul, g.map_mul, mul_assoc, mul_assoc, mul_left_comm (f y₁)])
        (λ y₁ y₂ ih₁ ih₂, by simp only [mul_add, linear_map.map_add, ih₁, ih₂]))
      (λ x₁ x₂ ih₁ ih₂, by simp only [add_mul, linear_map.map_add, ih₁, ih₂]),
    linear_map.map_add _⟩,
  commutes' := λ r, show lift iC.lmul (map f.to_linear_map g.to_linear_map (iA r ⊗ₜ 1)) = _,
    by rw [map_tmul, lift.tmul]; change f _ * g 1 = _; rw [f.commutes, g.map_one, mul_one] }
set_option class.instance_max_depth 32

theorem arec_tmul (f : iA →ₐ iC) (g : iB →ₐ iC) (p : iA.mod) (q : iB.mod) :
  arec f g (p ⊗ₜ q) = f p * g q :=
lift.tmul _ _

variables (iA iB iC)
def UMP : ((iA →ₐ iC) × (iB →ₐ iC)) ≃ (iA.tensor_product iB →ₐ iC) :=
{ to_fun := λ φ, arec φ.1 φ.2,
  inv_fun := λ φ, (φ.comp (iA.inl iB), φ.comp (iA.inr iB)),
  left_inv := λ ⟨φ₁, φ₂⟩, prod.ext
    (by ext p; change (arec φ₁ φ₂) (p ⊗ₜ 1) = φ₁ p;
      rw [arec_tmul, φ₂.map_one', mul_one])
    (by ext q; change (arec φ₁ φ₂) (1 ⊗ₜ q) = φ₂ q;
      rw [arec_tmul, φ₁.map_one', one_mul]),
  right_inv := λ φ, alg_hom.to_linear_map_inj $ tensor_product.ext $ λ p q,
    by dsimp only [alg_hom.to_linear_map_apply]; rw [arec_tmul,
      alg_hom.comp_apply, alg_hom.comp_apply, inl_def, inr_def, ← φ.map_mul, mul_def, mul_one, one_mul] }

variables {iA iB iC iD}
def amap (f : iA →ₐ iC) (g : iB →ₐ iD) : (iA.tensor_product iB) →ₐ (iC.tensor_product iD) :=
arec ((iC.inl iD).comp f) ((iC.inr iD).comp g)
variables (iA iB iC iD)

@[simp] lemma amap_tmul (f : iA →ₐ iC) (g : iB →ₐ iD) (x : A) (y : B) :
  amap f g (x ⊗ₜ y) = f x ⊗ₜ g y :=
by rw amap; simp only [arec_tmul,
  alg_hom.comp_apply, inl_def, inr_def, mul_def, mul_one, one_mul]

def aassoc : (iA.tensor_product iB).tensor_product iC →ₐ
  iA.tensor_product (iB.tensor_product iC) :=
arec (arec
  (iA.inl $ iB.tensor_product iC)
  ((iA.inr $ iB.tensor_product iC).comp $ iB.inl iC))
  ((iA.inr $ iB.tensor_product iC).comp $ iB.inr iC)

@[simp] lemma aassoc_tmul (x y z) :
  aassoc iA iB iC (x ⊗ₜ y ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) :=
by rw aassoc; simp only [arec_tmul, inl_def, inr_def, alg_hom.comp_apply, mul_def, mul_one, one_mul]

def id_tensor : (algebra.id R).tensor_product iA →ₐ iA :=
arec iA.of_id (alg_hom.id iA)

@[simp] lemma id_tensor_tmul (r x) : id_tensor iA (r ⊗ₜ x) = ((r : R) • x : iA.mod) :=
by rw id_tensor; simp only [arec_tmul, alg_hom.id_apply, of_id_apply, iA.smul_def]

def tensor_id : iA.tensor_product (algebra.id R) →ₐ iA :=
arec (alg_hom.id iA) iA.of_id

@[simp] lemma tensor_id_tmul (r x) : tensor_id iA (x ⊗ₜ r) = ((r : R) • x : iA.mod) :=
by rw tensor_id; simp only [arec_tmul, alg_hom.id_apply, of_id_apply, iA.smul_def, mul_comm]

def base_change_left : algebra iA.mod (iA.mod ⊗ iB.mod) :=
algebra.of_core { to_fun := iA.inl iB }

theorem base_change_left_apply (r : iA.mod) : base_change_left iA iB r = r ⊗ₜ 1 := rfl

set_option class.instance_max_depth 100
def base_change_left_rec {D : Type v₁} [comm_ring D] (iD : algebra iA.mod D)
  (φ : iB →ₐ iA.comap iD) : base_change_left iA iB →ₐ iD :=
{ to_fun := (tensor_product.lift (iA.comap iD).lmul).comp
    (map (iA.to_comap iD).to_linear_map φ.to_linear_map),
  hom := ⟨by simp only [comp_apply, one_def, map_tmul, alg_hom.to_linear_map_apply, lmul_apply,
      lift.tmul, φ.map_one', (to_comap iA iD).map_one']; apply mul_one,
    λ x y, tensor_product.induction_on _ _ x
      (by rw [zero_mul, linear_map.map_zero]; exact (zero_mul _).symm)
      (λ x₁ x₂, tensor_product.induction_on _ _ y
        (by rw [mul_zero, linear_map.map_zero]; exact (mul_zero _).symm)
        (λ y₁ y₂, by simp only [mul_def, comp_apply, map_tmul, alg_hom.to_linear_map_apply, lmul_apply,
          lift.tmul, (iA.to_comap iD).map_mul, φ.map_mul, mul_assoc]; rw mul_left_comm ((iA.to_comap iD) y₁))
        (λ y₁ y₂ ih₁ ih₂, by rw [mul_add, linear_map.map_add, ih₁, ih₂, linear_map.map_add, mul_add]))
      (λ x₁ x₂ ih₁ ih₂, by rw [add_mul, linear_map.map_add, ih₁, ih₂, linear_map.map_add, add_mul]),
    linear_map.map_add _⟩,
  commutes' := λ x, by rw [comp_apply, base_change_left_apply, map_tmul, alg_hom.to_linear_map_apply,
    alg_hom.to_linear_map_apply, to_comap_apply, lift.tmul, lmul_apply, φ.map_one']; exact mul_one _ }
set_option class.instance_max_depth 32

def base_change_right : algebra B (iA.mod ⊗ iB.mod) :=
algebra.of_core { to_fun := iA.inr iB }

end tensor_product
end algebra