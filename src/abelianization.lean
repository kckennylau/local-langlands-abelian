import group_theory.coset
import .topological_group
import .quotient_group

universes u v

set_option eqn_compiler.zeta true

def commutator_subgroup (G : Type u) [group G] (S : set G) : set G :=
{ z | ∃ L : list G, (∀ x ∈ L, ∃ p ∈ S, ∃ q ∈ S, x = p * q * p⁻¹ * q⁻¹) ∧ L.prod = z }

instance commutator_subgroup.subgroup
  (G : Type u) [group G] (S : set G) :
  is_subgroup (commutator_subgroup G S) :=
{ mul_mem := λ x y ⟨L1, h1, h2⟩ ⟨L2, h3, h4⟩, ⟨L1 ++ L2,
    list.forall_mem_append.2 ⟨h1, h3⟩,
    by simp [h2, h4]⟩,
  one_mem := ⟨[], by simp⟩,
  inv_mem := λ x ⟨L, h1, h2⟩, ⟨L.reverse.map has_inv.inv,
    λ x hx, let ⟨y, h3, h4⟩ := list.exists_of_mem_map hx in
      let ⟨p, hp, q, hq, h5⟩ := h1 y (list.mem_reverse.1 h3) in
      ⟨q, hq, p, hp, by rw [← h4, h5]; simp [mul_assoc]⟩,
    by rw ← h2; from list.rec_on L (by simp) (λ hd tl ih,
      by rw [list.reverse_cons', list.map_append, list.prod_append, ih]; simp)⟩ }

instance commutator_subgroup.normal_subgroup
  (G : Type u) [group G] (N : set G) [normal_subgroup N] :
  normal_subgroup (commutator_subgroup G N) :=
{ normal := λ x ⟨L, h1, h2⟩ g, ⟨L.map $ λ z, g * z * g⁻¹,
    λ x hx, let ⟨y, h3, h4⟩ := list.exists_of_mem_map hx in
      let ⟨p, hp, q, hq, h5⟩ := h1 y h3 in
      ⟨g * p * g⁻¹, normal_subgroup.normal _ hp _,
      g * q * g⁻¹, normal_subgroup.normal _ hq _,
      by rw [← h4, h5]; simp [mul_assoc]⟩,
    by rw ← h2; from list.rec_on L (by simp) (λ hd tl ih,
      by rw [list.map_cons, list.prod_cons, ih]; simp [mul_assoc])⟩ }

inductive abelianization.rel (G : Type u) [group G] : G → G → Prop
| basic : ∀ x y z w, abelianization.rel (x * y * z * w) (x * z * y * w)

def abelianization (G : Type u) [group G] : Type u :=
quot (abelianization.rel G)

def abelianization.mul (G : Type u) [group G] :
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

def abelianization.inv (G : Type u) [group G] :
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

instance abelianization.comm_group (G : Type u) [group G] :
  comm_group (abelianization G) :=
{ mul := abelianization.mul G,
  mul_assoc := by repeat { refine quot.ind (λ x, _) }; simp [abelianization.mul, mul_assoc],
  one := quot.mk _ 1,
  one_mul := by refine quot.ind (λ x, _); simp [abelianization.mul],
  mul_one := by refine quot.ind (λ x, _); change quot.mk _ (x * 1) = _; congr; apply mul_one,
  inv := abelianization.inv G,
  mul_left_inv := by refine quot.ind (λ x, _); simp [abelianization.mul, abelianization.inv]; refl,
  mul_comm := by refine quot.ind (λ x, _); refine quot.ind (λ y, _);
    change quot.mk _ (x * y) = quot.mk _ (y * x);
    suffices : quot.mk (rel G) (1 * x * y * 1) = quot.mk (rel G) (1 * y * x * 1);
    [simpa, from quot.sound ⟨_, _, _, _⟩] }

instance abelianization.comm_group' (G : Type u) [group G] :
  comm_group (quot (rel G)) :=
abelianization.comm_group G

instance abelianization.is_group_hom (G : Type u) [group G] :
  is_group_hom (quot.mk (rel G) : G → abelianization G) :=
⟨λ x y, rfl⟩

instance abelianization.topological_space (G : Type u)
  [t : topological_group G] : topological_space (abelianization G) :=
topological_space.coinduced (quot.mk _) t.to_topological_space

instance abelianization.topological_group (G : Type u) [topological_group G] :
  topological_group (abelianization G) :=
topological_group.coinduced (quot.mk (rel G)) quot.exists_rep $ λ S hs,
have (⋃ x : { x // quot.mk (rel G) x = 1}, (λ y, x.1 * y) ⁻¹' S)
    = quot.mk (rel G) ⁻¹' (quot.mk (rel G) '' S),
  from set.ext $ λ z,
  ⟨λ ⟨S, ⟨⟨g, h1⟩, rfl⟩, h2⟩, ⟨g * z, h2, by simp [is_group_hom.mul (quot.mk (rel G)), h1]⟩,
  λ ⟨g, h1, h2⟩, ⟨_, ⟨⟨g * z⁻¹, by simp [is_group_hom.mul (quot.mk (rel G)), is_group_hom.inv (quot.mk (rel G)), h2]⟩, rfl⟩, by simp [h1]⟩⟩,
this ▸ is_open_Union $ λ x : {x // quot.mk (rel G) x = 1},
continuous_mul continuous_const continuous_id _ hs

def Hausdorff_abelianization (G : Type u) [topological_group G] : Type u :=
left_cosets (closure ({1} : set (abelianization G)))

instance Hausdorff_abelianization.setoid (G : Type u)
  [topological_group G] : setoid (abelianization G) :=
left_rel (closure {1})

instance Hausdorff_abelianization.comm_group (G : Type u)
  [topological_group G] : comm_group (Hausdorff_abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂ x y $ λ m n,
    show ⟦m * n⟧ = ⟦n * m⟧, by rw mul_comm,
  .. quotient_group.group _ }

instance Hausdorff_abelianization.topological_space (G : Type u)
  [topological_group G] : topological_space (Hausdorff_abelianization G) :=
topological_space.coinduced quotient.mk (abelianization.topological_space G)

instance Hausdorff_abelianization.topological_group (G : Type u)
  [topological_group G] : topological_group (Hausdorff_abelianization G) :=
topological_group.coinduced quotient.mk quotient.exists_rep (λ S hs,
have (⋃ x : {x // ⟦x⟧ = 1}, (λ y, x.1 * y) ⁻¹' S)
    = quotient.mk ⁻¹' (quotient.mk '' S),
  from set.ext $ λ z,
  ⟨λ ⟨S, ⟨⟨g, h1⟩, rfl⟩, h2⟩, ⟨g * z, h2,
    by rw [is_group_hom.mul quotient.mk, h1, one_mul];
    from quotient_group.is_group_hom _⟩,
  λ ⟨g, h1, h2⟩, ⟨_, ⟨⟨g * z⁻¹,
    by rw [is_group_hom.mul quotient.mk, h2, is_group_hom.inv quotient.mk, mul_inv_self];
    repeat { from quotient_group.is_group_hom _ }⟩, rfl⟩,
    by simp [h1]⟩⟩,
this ▸ is_open_Union $ λ x : {x // ⟦x⟧ = 1},
continuous_mul continuous_const continuous_id _ hs)

def abelianization.induced {G : Type u} {H : Type v}
  [group G] [group H] (f : G → H) [is_group_hom f]
  (x : abelianization G) : abelianization H :=
quot.lift_on x (quot.mk (rel H) ∘ f) $ λ _ _ h,
by cases h with p q r s; apply quot.sound;
change rel H (f (p*q*r*s)) (f (p*r*q*s));
repeat { rw is_group_hom.mul f }; constructor

instance abelianization.induced.is_group_hom {G : Type u} {H : Type v}
  [group G] [group H] (f : G → H) [is_group_hom f] :
  is_group_hom (abelianization.induced f) :=
⟨by refine quot.ind (λ x, _); refine quot.ind (λ y, _);
rw ← is_group_hom.mul (quot.mk (rel G));
dsimp [abelianization.induced, quot.lift_on];
rw [is_group_hom.mul f]; refl⟩

theorem abelianization.induced.continuous {G : Type u} {H : Type v}
  [topological_group G] [topological_group H]
  (f : G → H) [hf : is_topological_group_hom f] :
  continuous (abelianization.induced f) :=
have H : quot.mk (rel H) ∘ f
    = abelianization.induced f ∘ quot.mk (rel G),
  from rfl,
continuous_coinduced_dom $ H ▸ hf.cts.comp continuous_coinduced_rng

instance abelianization.induced.is_topological_group_hom {G : Type u} {H : Type v}
  [topological_group G] [topological_group H]
  (f : G → H) [is_topological_group_hom f] :
  is_topological_group_hom (abelianization.induced f) :=
is_topological_group_hom.mk $ abelianization.induced.continuous f

def Hausdorff_abelianization.induced {G : Type u} {H : Type v}
  [topological_group G] [topological_group H]
  (f : G → H) [hf : is_topological_group_hom f]
  (x : Hausdorff_abelianization G) : Hausdorff_abelianization H :=
have H : ({1} : set (abelianization H)) = abelianization.induced f '' ({1} : set (abelianization G)),
  from by simp [is_group_hom.one (abelianization.induced f)],
quotient.lift_on x (quotient.mk ∘ abelianization.induced f) $
λ x y (h : x⁻¹ * y ∈ _), quotient.sound $ show _ * _ ∈ _,
by rw ← is_group_hom.inv (abelianization.induced f);
rw ← is_group_hom.mul (abelianization.induced f);
rw H; apply image_closure_subset_closure_image
  (abelianization.induced.continuous f) ⟨_, h, rfl⟩