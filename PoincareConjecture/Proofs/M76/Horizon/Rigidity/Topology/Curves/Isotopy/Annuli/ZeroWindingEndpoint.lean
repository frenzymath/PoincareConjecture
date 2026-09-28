import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.WindingCorrection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates

set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem depth_annulusCylinderHomeomorph (t : I) (z : Circle) :
    depth 8 (annulusCylinderHomeomorph (t, z) : P2) = 2 * (t : ℝ) - 1 := by
  rw [annulusCylinderHomeomorph_apply]
  exact depth_annulusMap (by norm_num)
    (by have hh : |2 * (t : ℝ) - 1| ≤ 1 := abs_le.mpr
          ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
        linarith) z

theorem annularIntegerTwist_fixed_rims (n : ℤ) (x : Ann)
    (hx : depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1) :
    annularIntegerTwist n x = x := by
  rcases hx with hx | hx
  · obtain ⟨z, rfl⟩ := (range_annulusRimPoint false).symm.subset hx
    exact annularIntegerTwist_rim n false z
  · obtain ⟨z, rfl⟩ := (range_annulusRimPoint true).symm.subset hx
    exact annularIntegerTwist_rim n true z

theorem annularIntegerTwist_mem_core_iff (n : ℤ) (x : Ann) :
    annularIntegerTwist n x ∈ range annulusCoreCircle ↔ x ∈ range annulusCoreCircle := by
  conv_lhs => rw [← annularIntegerTwist_core_image n]
  exact (annularIntegerTwist n).injective.mem_set_image

theorem annularIntegerTwist_depth (n : ℤ) (x : Ann) :
    depth 8 (annularIntegerTwist n x : P2) = depth 8 (x : P2) := by
  obtain ⟨⟨t, z⟩, rfl⟩ := annulusCylinderHomeomorph.surjective x
  rw [annularIntegerTwist_cylinder, depth_annulusCylinderHomeomorph, depth_annulusCylinderHomeomorph]

noncomputable def annularRadialImage (G : Ann ≃ₜ Ann) : C(I, Ann) :=
  ⟨fun t => G (annulusCylinderHomeomorph (t, 0)), by fun_prop⟩

theorem exists_finitePL_rim_fixed_radial_image
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hfix : ∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → G x = x) :
    ∃ f : ℝ → P2, FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) ∧
      (∀ t : I, f t = (annularRadialImage G t : P2)) ∧
      Function.Injective (annularRadialImage G) ∧
      annularRadialImage G 0 = annulusRimPoint false 0 ∧
      annularRadialImage G 1 = annulusRimPoint true 0 ∧
      ∀ t : I, (t : ℝ) ∈ Ioo (0 : ℝ) 1 →
        depth 8 (annularRadialImage G t : P2) ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨a, ha, _, hav, _, _⟩ := exists_finitePL_annularTwist_radial_arc 0
  have haRad (t : I) : a t = (annulusCylinderHomeomorph (t, 0) : P2) := by
    rw [hav, annularIntegerTwist_cylinder]
    simp only [Int.cast_zero, mul_zero, zero_mul, AddCircle.coe_zero, add_zero]
  obtain ⟨g, hg, hgv⟩ := hG
  have haMap : MapsTo a (Icc (0 : ℝ) 1) Ann := by
    intro t ht
    rw [haRad ⟨t, ht⟩]
    exact (annulusCylinderHomeomorph (⟨t, ht⟩, 0)).property
  refine ⟨g ∘ a, hg.comp ha haMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    change g (a t) = _
    rw [haRad, ← hgv]
    rfl
  · intro s t h
    exact congrArg Prod.fst (annulusCylinderHomeomorph.injective (G.injective h))
  · change G (annulusCylinderHomeomorph (0, 0)) = _
    rw [annulusCylinderHomeomorph_zero, hfix _ (Or.inl (depth_annulusRimPoint false 0))]
  · change G (annulusCylinderHomeomorph (1, 0)) = _
    rw [annulusCylinderHomeomorph_one, hfix _ (Or.inr (depth_annulusRimPoint true 0))]
  · intro t ht
    have hb := mem_squareAnnulus_iff_depth.mp (annularRadialImage G t).property
    have hne : depth 8 (annularRadialImage G t : P2) ≠ -1 ∧
        depth 8 (annularRadialImage G t : P2) ≠ 1 := by
      constructor <;> intro h
      all_goals
        have hy := hfix (annularRadialImage G t) (by first | exact Or.inl h | exact Or.inr h)
        have heq : annulusCylinderHomeomorph (t, 0) = annularRadialImage G t :=
          G.injective hy.symm
        have hd := congrArg (fun x : Ann => depth 8 (x : P2)) heq
        rw [depth_annulusCylinderHomeomorph, h] at hd
        linarith [ht.1, ht.2]
    exact ⟨lt_of_le_of_ne hb.1 hne.1.symm, lt_of_le_of_ne hb.2 hne.2⟩

theorem annularTwistPostcomposition_core_image_iff (G : Ann ≃ₜ Ann) (n : ℤ) (S : Set Ann) :
    (G.trans (annularIntegerTwist n)) '' S = range annulusCoreCircle ↔
      G '' S = range annulusCoreCircle := by
  change (fun x => annularIntegerTwist n (G x)) '' S = range annulusCoreCircle ↔ _
  rw [← image_image (annularIntegerTwist n) G S]
  conv_lhs => rhs; rw [← annularIntegerTwist_core_image n]
  exact (annularIntegerTwist n).injective.image_injective.eq_iff

theorem exists_zero_winding_annular_endpoint
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hfix : ∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → G x = x) :
    ∃ n : ℤ,
      let G' := G.trans (annularIntegerTwist (-n))
      G'.IsFinitePL ∧ G'.symm.IsFinitePL ∧
      (∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → G' x = x) ∧
      (∀ x : Ann, G' x ∈ range annulusCoreCircle ↔ G x ∈ range annulusCoreCircle) ∧
      (∀ S : Set Ann, G' '' S = range annulusCoreCircle ↔ G '' S = range annulusCoreCircle) ∧
      ∃ f r : ℝ → P2,
        FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) ∧
        (∀ t : I, f t = (annularRadialImage G' t : P2)) ∧
        Function.Injective (annularRadialImage G') ∧
        annularRadialImage G' 0 = annulusRimPoint false 0 ∧
        annularRadialImage G' 1 = annulusRimPoint true 0 ∧
        (∀ t : I, (t : ℝ) ∈ Ioo (0 : ℝ) 1 →
          depth 8 (annularRadialImage G' t : P2) ∈ Ioo (-1 : ℝ) 1) ∧
        FinitePiecewiseAffineOn r (Icc 0 1) ∧ InjOn r (Icc 0 1) ∧
        r 0 = (0, -1) ∧ r 1 = (0, 1) ∧
        (∀ t : I, (r t).2 = depth 8 (annularRadialImage G' t : P2)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1) ∧
        (∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) =
          (annularRadialImage G' t : P2)) ∧
        ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
          ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0 := by
  obtain ⟨f, hf, hfv, hinj, hzero, hone, hproper⟩ :=
    exists_finitePL_rim_fixed_radial_image G hG hfix
  obtain ⟨n, r, hr, hi, hr0, hr1, hdepth, hproj, htranslate⟩ :=
    exists_zero_winding_annular_arc_lift (annularRadialImage G) hinj f hf hfv hzero hone
  let G' := G.trans (annularIntegerTwist (-n))
  have hG' : G'.IsFinitePL := hG.trans (annularIntegerTwist_finitePL (-n))
  have hfix' (x : Ann) (hx : depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1) : G' x = x := by
    change annularIntegerTwist (-n) (G x) = x
    rw [hfix x hx]
    exact annularIntegerTwist_fixed_rims (-n) x hx
  obtain ⟨f', hf', hfv', hinj', hzero', hone', hproper'⟩ :=
    exists_finitePL_rim_fixed_radial_image G' hG' hfix'
  have hdepth' (t : I) : (r t).2 = depth 8 (annularRadialImage G' t : P2) :=
    (hdepth t).trans (annularIntegerTwist_depth (-n) (annularRadialImage G t)).symm
  refine ⟨n, hG', hG'.symm, hfix', fun x => annularIntegerTwist_mem_core_iff (-n) (G x),
    annularTwistPostcomposition_core_image_iff G (-n), f', r,
    hf', hfv', hinj', hzero', hone', hproper', hr, hi, hr0, hr1, hdepth', ?_, ?_, hproj, ?_⟩
  · intro t ht
    rw [hdepth' ⟨t, ht⟩]
    exact mem_squareAnnulus_iff_depth.mp (annularRadialImage G' ⟨t, ht⟩).property
  · intro t ht
    rw [hdepth' ⟨t, ht.1.le, ht.2.le⟩]
    exact hproper' ⟨t, ht.1.le, ht.2.le⟩ ht
  · intro s t hs ht k heq
    obtain ⟨hst, hk⟩ := htranslate ⟨s, hs⟩ ⟨t, ht⟩ k heq
    exact ⟨congrArg (fun u : I => (u : ℝ)) hst, hk⟩

end PoincareConjecture.M76.Dehn
