import data.finsupp algebra.pi_instances
import group_theory.coset
import .topological_group

noncomputable theory
local attribute [instance] classical.prop_decidable

universes u v w u₁

section group_cohomology

variables (G : Type u) [group G]
variables (M : Type v) [add_comm_group M]

@[reducible] def group_ring :=
additive G →₀ ℤ

instance group_ring.ring : ring (group_ring G) :=
finsupp.to_ring

instance group_ring.coe : has_coe G (group_ring G) :=
⟨λ g, finsupp.single g 1⟩

@[reducible] def group_module :=
module (group_ring G) M

variables {G M} [group_module G M]

class is_crossed_hom (f : G → M) : Prop :=
(mul : ∀ g h, f (g * h) = f g + g • f h)

def is_crossed_hom.add (f g : G → M)
  [is_crossed_hom f] [is_crossed_hom g] :
  is_crossed_hom (f + g) :=
⟨λ x y, show f (x * y) + g (x * y) = (f x + g x) + x • (f y + g y),
  by simp [is_crossed_hom.mul f, is_crossed_hom.mul g, smul_add]⟩

def is_crossed_hom.neg (f : G → M)
  [is_crossed_hom f] : is_crossed_hom (-f) :=
⟨λ x y, show -f (x * y) = -f x + x • (-f y),
  by simp [is_crossed_hom.mul f]⟩

variables (G M)

def crossed_hom :=
subtype (@is_crossed_hom G _ M _ _)

instance crossed_hom.to_is_crossed_hom
  (f : crossed_hom G M) : is_crossed_hom f.1 :=
f.2

instance crossed_hom.add_comm_group : add_comm_group (crossed_hom G M) :=
{ add := λ f g, ⟨f.1 + g.1, is_crossed_hom.add f.1 g.1⟩,
  add_assoc := λ f g h, subtype.eq $ add_assoc _ _ _,
  zero := ⟨λ x, 0, ⟨λ x y, by simp⟩⟩,
  zero_add := λ f, subtype.eq $ zero_add _,
  add_zero := λ f, subtype.eq $ add_zero _,
  neg := λ f, ⟨-f.1, is_crossed_hom.neg f.1⟩,
  add_left_neg := λ f, subtype.eq $ add_left_neg _,
  add_comm := λ f g, subtype.eq $ add_comm _ _ }

def principal_crossed_hom : set (crossed_hom G M) :=
{ f | ∃ m, ∀ x, f.1 x = x • m - m }

instance principal_crossed_hom.normal_subgroup :
  normal_add_subgroup (principal_crossed_hom G M) :=
{ add_mem := λ f g ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, λ x,
    show f.1 x + g.1 x = _, by simp [hm, hn, smul_add]⟩,
  zero_mem := ⟨0, λ x, by simp; refl⟩,
  neg_mem := λ f ⟨m, hm⟩, ⟨-m, λ x,
    show -f.1 x = _, by simp [hm]⟩,
  normal := λ f hf g, show g + f - g ∈ _, by simp [hf] }

def H1 : Type (max u v) :=
quotient_add_group.quotient (principal_crossed_hom G M)

instance H1.add_comm_group : add_comm_group (H1 G M) :=
quotient_add_group.add_comm_group _

end group_cohomology

variables (G : Type u) [topological_space G] [group G] [topological_group G]
variables (M : Type v) [topological_space M] [add_comm_group M] [topological_add_group M]

--set_option old_structure_cmd true

class topological_group_module extends module (group_ring G) M :=
(continuous_smul : continuous (λ m : G × M, (m.1 : group_ring G) • m.2))

variable [topological_group_module G M]

def H1c.set : set (H1 G M) :=
λ x, quotient.lift_on' x (λ f, continuous f.1) $ λ f g ⟨m, h⟩,
have H : ∀ (x : G), -(f.1 x) + (g.1 x) = ↑x • m - m := h,
have Hm : continuous (λ (x : G), ↑x • m),
  by change continuous ((λ m : G × M, (m.1 : group_ring G) • m.2) ∘ (λ x, (x, m)));
    letI := @prod.topological_space G M _ _;
    apply (continuous.prod_mk continuous_id continuous_const).comp
      (topological_group_module.continuous_smul G M),
propext ⟨λ hf,
  have H1 : g.1 = λ x, f.1 x + (x • m - m),
    from funext $ λ x, by rw ← H; simp [-add_comm],
  by rw H1; apply continuous_add hf (continuous_sub Hm continuous_const),
λ hg,
  have H1 : f.1 = λ x, g.1 x - (x • m - m),
    from funext $ λ x, by rw ← H; simp,
  by rw H1; apply continuous_sub hg (continuous_sub Hm continuous_const)⟩

instance H1c.is_add_subgroup : is_add_subgroup (H1c.set G M) :=
{ add_mem := λ x y, quotient.induction_on₂' x y $ λ f g hf hg,
    continuous_add hf hg,
  zero_mem := continuous_const,
  neg_mem := λ x, quotient.induction_on' x $ λ f hf,
    continuous_neg hf }

def H1c : Type (max u v) := H1c.set G M

instance H1c.add_comm_group : add_comm_group (H1c G M) :=
{ add_comm := λ f g, subtype.eq $ add_comm _ _,
  .. subtype.add_group }