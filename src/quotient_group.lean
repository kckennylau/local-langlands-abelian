import group_theory.coset

universes u v

set_option eqn_compiler.zeta true

def left_cosets.mul {G : Type u} [group G] (N : set G) [normal_subgroup N] :
  left_cosets N → left_cosets N → left_cosets N :=
by letI := left_rel N; from quotient.lift₂ (λ x y, ⟦x*y⟧)
  (assume a₁ a₂ b₁ b₂ : G,
  assume H1 : a₁⁻¹ * b₁ ∈ N,
  assume H2 : a₂⁻¹ * b₂ ∈ N,
  quotient.sound $ show (a₁ * a₂)⁻¹ * (b₁ * b₂) ∈ N,
  from calc (a₁ * a₂)⁻¹ * (b₁ * b₂)
      = (a₂⁻¹ * (a₁⁻¹ * b₁) * a₂⁻¹⁻¹) * (a₂⁻¹ * b₂) : by simp [mul_assoc]
  ... ∈ N : is_submonoid.mul_mem
    (normal_subgroup.normal _ H1 _) H2)

def left_cosets.inv {G : Type u} [group G] (N : set G) [normal_subgroup N] :
  left_cosets N → left_cosets N :=
by letI := left_rel N; from quotient.lift (λ x, ⟦x⁻¹⟧)
  (assume m n : G,
  assume H : m⁻¹ * n ∈ N,
  quotient.sound $ show m⁻¹⁻¹ * n⁻¹ ∈ N,
  from calc m⁻¹⁻¹ * n⁻¹
      = m * (m⁻¹ * n)⁻¹ * m⁻¹ : by simp [mul_assoc]
  ... ∈ N : normal_subgroup.normal _ (is_subgroup.inv_mem H) _)

instance quotient_group.group {G : Type u} [group G] (N : set G) [normal_subgroup N] :
  group (left_cosets N) :=
by letI := left_rel N; from
{ mul := left_cosets.mul N,
  mul_assoc := λ x y z, quotient.induction_on₃ x y z $ λ p q r,
    show ⟦p * q * r⟧ = ⟦p * (q * r)⟧, by rw mul_assoc,
  one := ⟦1⟧,
  one_mul := λ x, quotient.induction_on x $ λ m,
    show ⟦1 * m⟧ = ⟦m⟧, by rw one_mul,
  mul_one := λ x, quotient.induction_on x $ λ m,
    show ⟦m * 1⟧ = ⟦m⟧, by rw mul_one,
  inv := left_cosets.inv N,
  mul_left_inv := λ x, quotient.induction_on x $ λ m,
    show ⟦m⁻¹ * m⟧ = ⟦1⟧, by rw mul_left_inv }

instance quotient_group.group' {G : Type u} [group G] (N : set G) [normal_subgroup N] :
  group (quotient (left_rel N)) :=
quotient_group.group N

instance quotient_group.is_group_hom {G : Type u} [group G] (N : set G) [normal_subgroup N] :
  is_group_hom (@quotient.mk _ (left_rel N) : G → left_cosets N) :=
⟨λ x y, rfl⟩

def quotient_group.lift {G : Type u} {H : Type v} [group G] [group H]
  (N : set G) [normal_subgroup N] (f : G → H) [is_group_hom f]
  (hf : ∀ x ∈ N, f x = 1) (x : left_cosets N) : H :=
@quotient.lift_on _ _ (left_rel N) x f $ λ x y,
assume h : x⁻¹ * y ∈ N,
calc  f x = f x * f (x⁻¹ * y) : by simp [hf _ h]
      ... = f y : by simp [is_group_hom.mul f, is_group_hom.inv f]

def quotient_group.lift.is_group_hom {G : Type u} {H : Type v} [group G] [group H]
  (N : set G) [normal_subgroup N] (f : G → H) [is_group_hom f]
  (hf : ∀ x ∈ N, f x = 1) :
  is_group_hom (quotient_group.lift N f hf) :=
⟨λ x y, by letI := left_rel N; apply quotient.induction_on₂ x y; intros m n;
  change f (m * n) = f m * f n;
  from is_group_hom.mul f m n⟩