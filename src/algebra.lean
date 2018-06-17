import algebra.module

universes u v w

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
  c • x = algebra.f A c * x := rfl

class is_alg_hom {R : out_param $ Type u} {A : Type v} {B : Type w}
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B]
  (φ : A → B) extends is_ring_hom φ : Prop :=
(commute : ∀ r : R, φ r = r)

def alg_hom {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B] :=
{ φ : A → B // is_alg_hom φ }

instance alg_hom.to_is_alg_hom {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B]
  (φ : alg_hom A B) : is_alg_hom φ.val :=
φ.property

instance alg_hom.to_is_ring_hom {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B]
  (φ : alg_hom A B) : is_ring_hom φ.val :=
by apply_instance

instance alg_hom.has_coe_to_fun {R : out_param $ Type u} (A : Type v) (B : Type w)
  [out_param $ comm_ring R] [comm_ring A] [algebra R A]
  [comm_ring B] [algebra R B] :
  has_coe_to_fun (alg_hom A B) :=
⟨_, λ φ, φ.1⟩

def comm_ring.to_algebra (R : Type u) [comm_ring R] : algebra R R :=
{ f := id }