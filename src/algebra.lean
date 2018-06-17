import algebra.module

universes u v w u₁

class algebra (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] :=
(f : R → A) [hom : is_ring_hom f]

instance algebra.to_is_ring_hom (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] : is_ring_hom (algebra.f A) :=
algebra.hom A

instance algebra.to_has_coe (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] : has_coe R A :=
⟨algebra.f A⟩

instance algebra.to_is_ring_hom' (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] : is_ring_hom (coe : R → A) :=
algebra.hom A

@[simp] lemma algebra.coe_add (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  (r s : R) : ((r+s:R):A) = r + s :=
is_ring_hom.map_add _

@[simp] lemma algebra.coe_zero (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] :
  ((0:R):A) = 0 :=
is_ring_hom.map_zero _

@[simp] lemma algebra.coe_neg (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  (r : R) : ((-r:R):A) = -r :=
is_ring_hom.map_neg _

@[simp] lemma algebra.coe_sub (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  (r s : R) : ((r-s:R):A) = r - s :=
is_ring_hom.map_sub _

@[simp] lemma algebra.coe_mul (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  (r s : R) : ((r*s:R):A) = r * s :=
is_ring_hom.map_mul _

@[simp] lemma algebra.coe_one (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] :
  ((1:R):A) = 1 :=
is_ring_hom.map_one _

instance algebra.to_module (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] : module R A :=
{ smul := λ r x, r * x,
  smul_add := λ r x y, mul_add r x y,
  add_smul := λ r s x, by simp [add_mul],
  mul_smul := λ r s x, by simp [mul_assoc],
  one_smul := λ x, by simp [one_mul] }

theorem algebra.smul_def (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] (c : R) (x : A) :
  c • x = c * x := rfl

theorem is_linear_map.mul_left (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] (x : A) :
  is_linear_map (λ y, x * y) :=
is_linear_map.mk (mul_add x) (λ _, mul_left_comm x _)

theorem is_linear_map.mul_right (R : out_param $ Type u) (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] (y : A) :
  is_linear_map (λ x, x * y) :=
is_linear_map.mk (λ _ _, add_mul _ _ y) (λ _ _, mul_assoc _ _ y)

class is_alg_hom {R : out_param $ Type u} {A : Type v} {B : Type w}
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B]
  (φ : A → B) extends is_ring_hom φ : Prop :=
(commute : ∀ r : R, φ r = r)

instance is_alg_hom.id {R : out_param $ Type u} {A : Type v}
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] : is_alg_hom (id : A → A) :=
is_alg_hom.mk $ λ _, rfl

instance is_alg_hom.comp {R : out_param $ Type u} {A : Type v} {B : Type w} {C : Type u₁}
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B] [comm_ring C] [algebra R C]
  (f : B → C) (g : A → B) [is_alg_hom f] [is_alg_hom g] :
  is_alg_hom (f ∘ g) :=
is_alg_hom.mk $ λ r, by simp [is_alg_hom.commute g, is_alg_hom.commute f]

def alg_hom {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B] :=
{ φ : A → B // is_alg_hom φ }

instance alg_hom.to_is_alg_hom {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B]
  (φ : alg_hom A B) : is_alg_hom φ.1 :=
φ.property

def alg_hom.id {R : out_param $ Type u} (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] : alg_hom A A :=
⟨id, is_alg_hom.id⟩

def alg_hom.comp {R : out_param $ Type u} {A : Type v} {B : Type w} {C : Type u₁}
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B] [comm_ring C] [algebra R C]
  (f : alg_hom B C) (g : alg_hom A B) : alg_hom A C :=
⟨f.1 ∘ g.1, is_alg_hom.comp f.1 g.1⟩

@[simp] lemma alg_hom.id.val {R : out_param $ Type u} (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] (x : A) :
  (alg_hom.id A).1 x = x :=
rfl

@[simp] lemma alg_hom.comp.val {R : out_param $ Type u} {A : Type v} {B : Type w} {C : Type u₁}
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B] [comm_ring C] [algebra R C]
  (f : alg_hom B C) (g : alg_hom A B) (x : A) :
  (alg_hom.comp f g).1 x = f.1 (g.1 x) :=
rfl

instance alg_hom.to_is_ring_hom {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B]
  (φ : alg_hom A B) : is_ring_hom φ.1 :=
by apply_instance

instance alg_hom.has_coe_to_fun {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B] :
  has_coe_to_fun (alg_hom A B) :=
⟨_, λ φ, φ.1⟩

theorem is_alg_hom.to_is_linear_map {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B]
  (φ : A → B) [is_alg_hom φ] : is_linear_map φ :=
is_linear_map.mk (λ _ _, is_ring_hom.map_add φ) $ λ _ _,
by simp [algebra.smul_def, is_ring_hom.map_mul φ, is_alg_hom.commute φ]

def comm_ring.to_algebra (R : Type u) [comm_ring R] : algebra R R :=
{ f := id }

local attribute [instance] comm_ring.to_algebra

def alg_hom.f {R : out_param $ Type u} (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] : alg_hom R A :=
⟨algebra.f A, @is_alg_hom.mk _ _ _ _ _ _ _ _ _ (algebra.to_is_ring_hom R A) (λ r, rfl)⟩

@[simp] lemma alg_hom.f.val {R : out_param $ Type u} (A : Type v)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A] (r : R) :
  (alg_hom.f A).1 r = r :=
rfl