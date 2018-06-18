import analysis.topology.topological_structures
import analysis.topology.continuity
import analysis.complex
import algebra.pi_instances
import group_theory.coset
import .quotient_group

universes u v

instance subtype.val.is_group_hom (α : Type u) [group α]
  (S : set α) [is_subgroup S] : is_group_hom (subtype.val : S → α) :=
⟨λ _ _, rfl⟩

class topological_group (α : Type u) extends topological_space α, group α, topological_monoid α :=
(continuous_inv : continuous (λ p : α, p⁻¹))

theorem continuous_inv {α : Type u} [topological_group α] :
  continuous (λ p : α, p⁻¹) :=
topological_group.continuous_inv α

theorem continuous_mul_inv (α : Type u) [topological_group α] :
  continuous (λ p : α × α, p.1 * p.2 ⁻¹) :=
continuous_mul continuous_fst $ continuous_snd.comp continuous_inv

instance topological_group.t1_to_t2 (α : Type u)
  [topological_group α] [t1_space α] : t2_space α :=
⟨λ x y Hxy,
let ⟨u, v, hu, hv, hxu, hyv, h⟩ := is_open_prod_iff.1
  (continuous_mul_inv _ _
  (t1_space.t1 (1:α))) x y
  (λ H, Hxy $ calc x = x * y⁻¹ * y : by simp ... = y : by simp at H; rw H; simp) in
⟨u, v, hu, hv, hxu, hyv, set.eq_empty_of_subset_empty $
  λ z ⟨h1, h2⟩, @h (z, z) ⟨h1, h2⟩ (by simp)⟩⟩

theorem continuous_conj {α : Type u} [topological_group α] {y : α} :
  continuous (λ x, y * x * y⁻¹) :=
continuous_mul (continuous_mul continuous_const continuous_id) continuous_const

instance topological_group.one_closure.normal_subgroup
  (α : Type u) [topological_group α] :
  normal_subgroup (closure ({1} : set α)) :=
{ mul_mem := λ x y hx hy S ⟨hs1, hs2⟩,
    have H1 : _ := continuous_iff_is_closed.1 (topological_monoid.continuous_mul α) S hs1,
    have H2 : closure (set.prod ({1} : set α) ({1} : set α)) = _ := closure_prod_eq,
    have H3 : (x, y) ∈ closure (set.prod ({1} : set α) ({1} : set α)),
      from H2.symm ▸ ⟨hx, hy⟩,
    H3 _ ⟨H1, by simpa using hs2⟩,
  one_mem := λ _ ⟨_, H⟩, by simpa using H,
  inv_mem := λ _ H S ⟨hs1, hs2⟩, H _
    ⟨continuous_iff_is_closed.1
      continuous_inv _ hs1,
    show ({1} : set α) ⊆ { x | x⁻¹ ∈ S },
      by simpa using hs2⟩,
  normal := λ x H y S ⟨hs1, hs2⟩, H _
    ⟨continuous_iff_is_closed.1 continuous_conj _ hs1,
    show ({1} : set α) ⊆ { x | y * x * y⁻¹ ∈ S },
      by simpa using hs2⟩ }

def topological_group.induced (α : Type u) (β : Type v)
  [group α] [t : topological_group β]
  (f : α → β) [is_group_hom f] :
  topological_group α :=
by letI := topological_space.induced f t.to_topological_space; from
{ continuous_mul := continuous_induced_rng $
    suffices (f ∘ λ p : α × α, p.1 * p.2)
      = (λ p : α × α, f (p.1) * f (p.2)),
    by rw this; from continuous_mul
      (continuous_fst.comp continuous_induced_dom)
      (continuous_snd.comp continuous_induced_dom),
    funext $ λ p, is_group_hom.mul f _ _,
  continuous_inv := continuous_induced_rng $
    suffices (f ∘ has_inv.inv) = (λ p, (f p)⁻¹),
    by rw this; from continuous_induced_dom.comp continuous_inv,
    funext $ λ p, is_group_hom.inv f _ }

lemma continuous_apply' {ι : Type u} {π : ι → Type v}
  [∀i, topological_space (π i)] (i : ι) :
  continuous (λp:Πi, π i, p i) :=
continuous_supr_dom continuous_induced_dom

instance Pi.topological_group {ι : Type u}
  {β : ι → Type v} [Π i, topological_group (β i)] :
  topological_group (Π i, β i) :=
{ continuous_mul := continuous_pi $ λ i, continuous_mul
    (continuous_fst.comp (continuous_apply' i))
    (continuous_snd.comp (continuous_apply' i)),
  continuous_inv := continuous_pi $ λ i,
    show continuous (λ p : Π i, β i, (p i)⁻¹),
    from (continuous_apply' i).comp continuous_inv }

def topological_group.coinduced {α : Type u} {β : Type v}
  [t : topological_group α] [group β]
  (f : α → β) [is_group_hom f] (hf1 : function.surjective f)
  (hf2 : ∀ S, is_open S → is_open (f ⁻¹' (f '' S))) :
  topological_group β :=
{ continuous_mul :=
  by letI := topological_space.coinduced f t.to_topological_space; from
  have @prod.topological_space β β
        (@topological_space.coinduced α β f _)
        (@topological_space.coinduced α β f _)
    = @topological_space.coinduced (α × α) (β × β)
        (λ p, (f p.1, f p.2)) prod.topological_space,
  from have H1 : prod.fst ∘ (λ p : α × α, (f p.1, f p.2)) = f ∘ prod.fst,
    from rfl,
  have H2 : prod.snd ∘ (λ p : α × α, (f p.1, f p.2)) = f ∘ prod.snd,
    from rfl,
  have H3 : topological_space.induced f (topological_space.coinduced f _)
      ≤ t.to_topological_space,
    from induced_le_iff_le_coinduced.2 (le_refl _),
  le_antisymm
    (lattice.sup_le
      (induced_le_iff_le_coinduced.1 (by rw [induced_compose, H1, ← induced_compose];
        from le_trans (induced_mono H3) lattice.le_sup_left))
      (induced_le_iff_le_coinduced.1 (by rw [induced_compose, H2, ← induced_compose];
        from le_trans (induced_mono H3) lattice.le_sup_right)))
    (λ S hs, is_open_prod_iff.2 $ λ x y hxy,
    let ⟨m, hm⟩ := hf1 x, ⟨n, hn⟩ := hf1 y in
    let ⟨u, v, hu, hv, hmu, hnv, H⟩ := is_open_prod_iff.1 hs m n (by simpa [hm, hn] using hxy) in
    ⟨f '' u, f '' v, hf2 u hu, hf2 v hv, ⟨m, hmu, hm⟩, ⟨n, hnv, hn⟩,
      λ ⟨p, q⟩ ⟨⟨P, hp1, hp2⟩, ⟨Q, hq1, hq2⟩⟩,
      by simp at hp2 hq2; rw [← hp2, ← hq2]; from @H (P, Q) ⟨hp1, hq1⟩⟩),
  have H1 : (λ p : α × α, f p.1 * f p.2) = f ∘ (λ p : α × α, p.1 * p.2),
    from funext $ λ ⟨p, q⟩, eq.symm $ is_group_hom.mul f _ _,
  by rw this; from continuous_coinduced_dom
    (show continuous (λ p : α × α, f p.1 * f p.2),
    by rw H1; from continuous_mul'.comp continuous_coinduced_rng),
  continuous_inv := continuous_coinduced_dom $
    by letI := topological_space.coinduced f t.to_topological_space; from
    have H : (λ p, p⁻¹) ∘ f = f ∘ (λ p, p⁻¹),
      from funext $ λ _, eq.symm $ is_group_hom.inv f _,
    show continuous ((λ p, p⁻¹) ∘ f),
    by rw H; from continuous_inv.comp continuous_coinduced_rng,
  .. topological_space.coinduced f t.to_topological_space }

class topological_field (α : Type u)
  extends topological_space α, field α, topological_ring α :=
(continuous_inv : @continuous _ _
  (topological_space.induced units.val to_topological_space)
  (topological_space.induced units.val to_topological_space)
  (λ (p : units α), p⁻¹))

instance topological_field.units.topological_group
  (α : Type u) [topological_field α] :
  topological_group (units α) :=
by letI : topological_space (units α) :=
  topological_space.induced units.val (by apply_instance); from
have H1 : @prod.topological_space (units α) (units α)
      (topological_space.induced units.val (by apply_instance))
      (topological_space.induced units.val (by apply_instance))
  = topological_space.induced
      (λ p : units α × units α, (p.1.1, p.2.1))
      prod.topological_space,
by simp [prod.topological_space, induced_sup, induced_compose],
have H2 : units.val ∘ (λ (p : units α × units α), p.1 * p.2)
  = λ p : units α × units α, p.1.1 * p.2.1,
by funext p; cases p with p q; cases p; cases q; refl,
{ continuous_mul := by rw H1; apply continuous_induced_rng;
    rw H2; apply continuous_mul; apply continuous.comp;
    [{rw ← H1, apply continuous_fst}, from continuous_induced_dom,
     {rw ← H1, apply continuous_snd}, from continuous_induced_dom],
  continuous_inv := topological_field.continuous_inv α }

class is_topological_group_hom {α : Type u} {β : Type v}
  [topological_group α] [topological_group β]
  (f : α → β) extends is_group_hom f : Prop :=
(cts : continuous f)

def topological_group_hom (α : Type u) (β : Type v)
  [topological_group α] [topological_group β] :=
subtype (@is_topological_group_hom α β)

structure topological_group_isomorphism (α : Type u) (β : Type v)
  [topological_group α] [topological_group β] extends α ≃ β :=
(hom_to_fun : is_topological_group_hom to_fun)
(hom_inv_fun : is_topological_group_hom inv_fun)

instance topological_group.preimage
  (α : Type u) (β : Type v)
  [topological_group α] [topological_group β]
  (f : α → β) [is_topological_group_hom f]
  (s : set β) [is_subgroup s] : topological_group (f ⁻¹' s) :=
topological_group.induced _ _ subtype.val

instance topological_group.closure.normal_subgroup
  (α : Type u) [topological_group α]
  (N : set α) [normal_subgroup N] :
  normal_subgroup (closure N) :=
{ mul_mem := λ x y hx hy S ⟨hs1, hs2⟩,
    have H1 : _ := continuous_iff_is_closed.1 (topological_monoid.continuous_mul α) S hs1,
    have H2 : closure (set.prod N N) = _ := closure_prod_eq,
    have H3 : (x, y) ∈ closure (set.prod N N),
      from H2.symm ▸ ⟨hx, hy⟩,
    H3 _ ⟨H1, λ ⟨p, q⟩ ⟨hp, hq⟩, hs2 $ is_submonoid.mul_mem hp hq⟩,
  one_mem := subset_closure $ is_submonoid.one_mem N,
  inv_mem := λ x hx S ⟨hs1, hs2⟩, hx _
    ⟨continuous_iff_is_closed.1 continuous_inv _ hs1,
    λ z hz, @hs2 z⁻¹ $ is_subgroup.inv_mem hz⟩,
  normal := λ x hx g S ⟨hs1, hs2⟩, hx _
    ⟨continuous_iff_is_closed.1 continuous_conj _ hs1,
    λ z hz, @hs2 (g * z * g⁻¹) $
      normal_subgroup.normal _ hz _⟩ }

set_option eqn_compiler.zeta true

instance quotient_group.topological_group (G : Type u)
  [topological_group G] (N : set G) [normal_subgroup N] :
  topological_group (left_cosets N) :=
by letI := left_rel N; from
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

noncomputable instance : topological_field ℂ :=
{ continuous_inv :=
    have H : (units.val ∘ λ (p : units ℂ), p⁻¹)
        = λ p, p.1⁻¹,
      from funext $ λ x, units.inv_eq_inv x,
    by apply continuous_induced_rng; rw H;
      apply continuous_iff_tendsto.2; intro x;
      cases x with x y h1 h2;
      apply filter.tendsto.comp
        (continuous_iff_tendsto.1 continuous_induced_dom _)
        (complex.tendsto_inv _);
      simp; intro H; simp [H] at h1; assumption }