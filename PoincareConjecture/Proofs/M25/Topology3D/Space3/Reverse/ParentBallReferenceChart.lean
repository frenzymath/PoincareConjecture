import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceVertical
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import Mathlib.Topology.Compactness.Compact












set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D


noncomputable def referenceCompressedDiffeomorph
    (a : ℝ) (ha : a ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) :
    Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞ := by
  let V : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ)
      (E2 × ℝ) (E2 × ℝ) ∞ := {
    toEquiv := {
      toFun := fun p => (p.1, f p.2)
      invFun := fun p => (p.1, f.symm p.2)
      left_inv := fun p => Prod.ext rfl (f.symm_apply_apply p.2)
      right_inv := fun p => Prod.ext rfl (f.apply_symm_apply p.2) }
    contMDiff_toFun := (contDiff_fst.prodMk
      (f.contMDiff_toFun.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (f.contMDiff_invFun.contDiff.comp contDiff_snd)).contMDiff }
  exact (heightCoordinates.toDiffeomorph.trans
    (referenceFlatteningDiffeomorph a ha α hα hpos)).trans V


theorem referenceCompressedDiffeomorph_apply
    (a : ℝ) (ha : a ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (y : E3) :
    referenceCompressedDiffeomorph a ha α hα hpos f y =
      (α (heightCoordinates y).2 • (heightCoordinates y).1,
        f ((heightCoordinates y).2 - referenceCapHeight a
          (α (heightCoordinates y).2 • (heightCoordinates y).1))) := rfl


theorem referenceCompressedDiffeomorph_symm_apply
    (a : ℝ) (ha : a ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (p : E2 × ℝ) :
    (referenceCompressedDiffeomorph a ha α hα hpos f).symm p =
      heightCoordinates.symm
        ((α (f.symm p.2 + referenceCapHeight a p.1))⁻¹ • p.1,
          f.symm p.2 + referenceCapHeight a p.1) := rfl


theorem exists_reference_chart_cylinder
    (C : OpenPartialHomeomorph (E2 × ℝ) E3) (H b : ℝ) (hb : 0 < b)
    (hzero : Metric.closedBall (0 : E2) H ×ˢ ({0} : Set ℝ) ⊆ C.source) :
    ∃ η > (0 : ℝ), η < b ∧
      Metric.closedBall (0 : E2) H ×ˢ Set.Icc (-η) η ⊆ C.source := by
  obtain ⟨U, V, _, hV, hHU, h0V, hUV⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : E2) H)
      (isCompact_singleton (x := (0 : ℝ))) C.open_source hzero
  have hVzero : V ∈ 𝓝 (0 : ℝ) := hV.mem_nhds (h0V (mem_singleton 0))
  obtain ⟨d, hd, hdV⟩ := Metric.mem_nhds_iff.mp hVzero
  let η := min d b / 2
  have hmin : 0 < min d b := lt_min hd hb
  have hη : 0 < η := div_pos hmin (by norm_num)
  have hηd : η < d := by
    dsimp only [η]
    linarith only [min_le_left d b, hmin]
  have hηb : η < b := by
    dsimp only [η]
    linarith only [min_le_right d b, hmin]
  refine ⟨η, hη, hηb, ?_⟩
  intro p hp
  apply hUV
  refine ⟨hHU hp.1, hdV ?_⟩
  have hpabs : |p.2| ≤ η := abs_le.mpr hp.2
  exact mem_ball_zero_iff.mpr
    (by simpa only [Real.norm_eq_abs] using hpabs.trans_lt hηd)


theorem referenceCompressedDiffeomorph_model_bounds
    (a : ℝ) (ha : a ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (H η : ℝ) (hH : 0 ≤ H)
    (hradial : ∀ z, |z| < 1 → α z * Real.sqrt (1 - z ^ 2) ≤ H)
    (hcompare : ∀ z, -1 < z → z ≤ 1 →
      α z ≤ referenceCapScale a / (1 + z))
    (f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hfzero : f 0 = 0) (hfmono : StrictMono f)
    (hfthin : ∀ z : ℝ, z ∈ Set.Icc (-2 : ℝ) 0 → f z ∈ Set.Ioc (-η) 0) :
    (∀ y ∈ Metric.closedBall (0 : E3) 1,
      ‖(referenceCompressedDiffeomorph a ha α hα hpos f y).1‖ ≤ H ∧
      (referenceCompressedDiffeomorph a ha α hα hpos f y).2 ∈ Set.Ioc (-η) 0) ∧
    ∀ y ∈ Metric.ball (0 : E3) 1,
      (referenceCompressedDiffeomorph a ha α hα hpos f y).2 ∈ Set.Ioo (-η) 0 := by
  have hclosed : ∀ y ∈ Metric.closedBall (0 : E3) 1,
      ‖(referenceCompressedDiffeomorph a ha α hα hpos f y).1‖ ≤ H ∧
      (referenceCompressedDiffeomorph a ha α hα hpos f y).2 ∈ Set.Ioc (-η) 0 := by
    intro y hy
    have hsq : ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 ≤ 1 := by
      rw [← heightCoordinates_norm_sq]
      have hynorm := mem_closedBall_zero_iff.mp hy
      nlinarith only [hynorm, norm_nonneg y]
    refine ⟨reference_profile_horizontal_norm_le α H hpos hH hradial
      (heightCoordinates y).1 (heightCoordinates y).2 hsq, ?_⟩
    exact hfthin _
      (referenceFlattening_snd_mem_Icc a ha α hα hpos hcompare (heightCoordinates y) hsq)
  refine ⟨hclosed, ?_⟩
  intro y hy
  have hsq : ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 < 1 := by
    rw [← heightCoordinates_norm_sq]
    have hynorm := mem_ball_zero_iff.mp hy
    nlinarith only [hynorm, norm_nonneg y]
  refine ⟨(hclosed y (ball_subset_closedBall hy)).2.1, ?_⟩
  have hneg := referenceFlattening_snd_neg a ha α hα hpos hcompare
    (heightCoordinates y) hsq
  change f ((referenceFlatteningDiffeomorph a ha α hα hpos
    (heightCoordinates y)).2) < 0
  simpa only [hfzero] using hfmono hneg


theorem referenceCompressedDiffeomorph_cap_germ
    (a : ℝ) (ha : a ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (c₂ : ℝ) (hc₂a : c₂ < a)
    (heq : ∀ z, c₂ ≤ z → α z = referenceCapScale a / (1 + z))
    (η : ℝ) (hη : 0 < η)
    (f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hfnear : ∀ z : ℝ, |z| ≤ η / 8 → f z = z) :
    (∀ X : E2, c₂ ≤ referenceCapHeight a X →
      referenceCompressedDiffeomorph a ha α hα hpos f (referenceCapPoint a X) =
        (X, 0)) ∧
    ∀ᶠ y in 𝓝ˢ {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2},
      referenceCompressedDiffeomorph a ha α hα hpos f y =
        referenceFlatteningDiffeomorph a ha α hα hpos (heightCoordinates y) := by
  let F0 : E3 → E2 × ℝ := fun y =>
    referenceFlatteningDiffeomorph a ha α hα hpos (heightCoordinates y)
  have hfzero : f 0 = 0 := hfnear 0 (by rw [abs_zero]; positivity)
  have hcap : ∀ X : E2, c₂ ≤ referenceCapHeight a X →
      referenceCompressedDiffeomorph a ha α hα hpos f (referenceCapPoint a X) =
        (X, 0) := by
    intro X hX
    have hflat : F0 (referenceCapPoint a X) = (X, 0) :=
      referenceFlattening_capPoint a ha α hα hpos c₂ heq X hX
    change ((F0 (referenceCapPoint a X)).1, f (F0 (referenceCapPoint a X)).2) = (X, 0)
    rw [hflat, hfzero]
  let W : Set E3 := {y | |(F0 y).2| < η / 8}
  have hF0 : Continuous F0 :=
    (referenceFlatteningDiffeomorph a ha α hα hpos).contMDiff_toFun.contDiff.continuous.comp
      heightCoordinates.continuous
  have hWopen : IsOpen W := isOpen_lt hF0.snd.abs continuous_const
  have hDW : {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} ⊆ W := by
    intro y hy
    rw [← referenceCapPoint_image_closedBall a ha] at hy
    obtain ⟨X, hX, rfl⟩ := hy
    have hXa : a ≤ referenceCapHeight a X := by
      simpa only [referenceCapPoint, heightCoordinates.apply_symm_apply] using
        (referenceCapPoint_cap_iff a ha X).mpr (mem_closedBall_zero_iff.mp hX)
    have hflat : F0 (referenceCapPoint a X) = (X, 0) :=
      referenceFlattening_capPoint a ha α hα hpos c₂ heq X (hc₂a.le.trans hXa)
    change |(F0 (referenceCapPoint a X)).2| < η / 8
    rw [hflat]
    simpa only [abs_zero] using div_pos hη (by norm_num : (0 : ℝ) < 8)
  refine ⟨hcap, ?_⟩
  filter_upwards [hWopen.mem_nhdsSet.mpr hDW] with y hy
  have hy' : |(F0 y).2| ≤ η / 8 := (show |(F0 y).2| < η / 8 from hy).le
  change ((F0 y).1, f (F0 y).2) = F0 y
  rw [hfnear _ hy']


theorem exists_reference_ball_chart
    (C : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hC : ContDiffOn ℝ ∞ C C.source)
    (hCi : ContDiffOn ℝ ∞ C.symm C.target)
    (a ε b : ℝ) (ha : a ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hε : 0 < ε) (hb : 0 < b)
    (hzero : Metric.closedBall (0 : E2) (1 + ε) ×ˢ ({0} : Set ℝ) ⊆ C.source) :
    ∃ H c₂ η : ℝ,
      1 < H ∧ H < 1 + ε ∧ c₂ ∈ Set.Ioo (1 / 2 : ℝ) a ∧
      0 < η ∧ η < b ∧
      Metric.closedBall (0 : E2) H ×ˢ Set.Icc (-η) η ⊆ C.source ∧
      ∃ α : ℝ → ℝ, ∃ hα : ContDiff ℝ ∞ α, ∃ hpos : ∀ z, 0 < α z,
        (∀ z, c₂ ≤ z → α z = referenceCapScale a / (1 + z)) ∧
        (∀ z, |z| < 1 → α z * Real.sqrt (1 - z ^ 2) ≤ H) ∧
        (∀ z, -1 < z → z ≤ 1 → α z ≤ referenceCapScale a / (1 + z)) ∧
        ∃ f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
          f 0 = 0 ∧ StrictMono f ∧
          (∀ z : ℝ, |z| ≤ η / 8 → f z = z) ∧
          (∀ z : ℝ, z ∈ Set.Icc (-2 : ℝ) 0 → f z ∈ Set.Ioc (-η) 0) ∧
          ∃ B : BallNeighborhoodChart E3 E3,
            let D := referenceCompressedDiffeomorph a ha α hα hpos f
            let F0 : E3 → E2 × ℝ := fun y =>
              referenceFlatteningDiffeomorph a ha α hα hpos (heightCoordinates y)
            B.chart = D.toHomeomorph.toOpenPartialHomeomorph.trans C ∧
            B.chart.source = D ⁻¹' C.source ∧ B.chart.target = C.target ∧
            (∀ y : E3, B.chart y = C (D y)) ∧
            (∀ Y : E3, B.chart.symm Y =
              heightCoordinates.symm
                ((α (f.symm (C.symm Y).2 + referenceCapHeight a (C.symm Y).1))⁻¹ •
                    (C.symm Y).1,
                  f.symm (C.symm Y).2 + referenceCapHeight a (C.symm Y).1)) ∧
            (∀ y ∈ Metric.closedBall (0 : E3) 1,
              ‖(D y).1‖ ≤ H ∧ (D y).2 ∈ Set.Ioc (-η) 0) ∧
            (∀ y ∈ Metric.ball (0 : E3) 1, (D y).2 ∈ Set.Ioo (-η) 0) ∧
            B.closedRegion ⊆ C '' (Metric.closedBall (0 : E2) H ×ˢ Set.Ioc (-η) 0) ∧
            B.inside ⊆ C '' (Metric.closedBall (0 : E2) H ×ˢ Set.Ioo (-η) 0) ∧
            (∀ X : E2, c₂ ≤ referenceCapHeight a X →
              B.chart (referenceCapPoint a X) = C (X, 0)) ∧
            (∀ X : E2, ‖X‖ ≤ 1 → B.chart (referenceCapPoint a X) = C (X, 0)) ∧
            ∀ᶠ y in 𝓝ˢ {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2},
              y ∈ B.chart.source ∧ F0 y ∈ C.source ∧ B.chart y = C (F0 y) := by
  obtain ⟨H, c₁, c₂, hH, hHε, _, _, hc₁, hc₁₂, hc₂a,
      α, hα, hpos, heq, hradial, hcompare⟩ := exists_reference_cap_profile a ε ha hε
  have hHnonneg : 0 ≤ H := zero_le_one.trans hH.le
  have hzeroH : Metric.closedBall (0 : E2) H ×ˢ ({0} : Set ℝ) ⊆ C.source := by
    intro p hp
    exact hzero ⟨closedBall_subset_closedBall hHε.le hp.1, hp.2⟩
  obtain ⟨η, hη, hηb, hcylinder⟩ := exists_reference_chart_cylinder C H b hb hzeroH
  obtain ⟨f, hfzero, hfmono, hfnear, hfthin⟩ :=
    exists_reference_vertical_diffeomorph 2 η (by norm_num) hη
  let D := referenceCompressedDiffeomorph a ha α hα hpos f
  obtain ⟨hclosed, hopen⟩ := referenceCompressedDiffeomorph_model_bounds
    a ha α hα hpos H η hHnonneg hradial hcompare f hfzero hfmono hfthin
  let B : BallNeighborhoodChart E3 E3 := {
    chart := D.toHomeomorph.toOpenPartialHomeomorph.trans C
    closedBall_subset_source := by
      intro y hy
      refine ⟨mem_univ y, hcylinder ?_⟩
      exact ⟨mem_closedBall_zero_iff.mpr (hclosed y hy).1,
        (hclosed y hy).2.1.le, (hclosed y hy).2.2.trans hη.le⟩
    smooth := hC.comp D.contMDiff_toFun.contDiff.contDiffOn (fun _ hx => hx.2)
    smooth_symm := D.contMDiff_invFun.contDiff.comp_contDiffOn
      (hCi.mono (fun _ hy => hy.1)) }
  obtain ⟨hcap, hgerm⟩ := referenceCompressedDiffeomorph_cap_germ
    a ha α hα hpos c₂ hc₂a heq η hη f hfnear
  refine ⟨H, c₂, η, hH, hHε, ⟨hc₁.trans hc₁₂, hc₂a⟩, hη, hηb,
    hcylinder, α, hα, hpos, heq, hradial, hcompare,
    f, hfzero, hfmono, hfnear, hfthin, B, rfl, ?_, ?_, ?_, ?_,
    hclosed, hopen, ?_, ?_, ?_, ?_, ?_⟩
  · ext y
    change (y ∈ (Set.univ : Set E3) ∧ D y ∈ C.source) ↔ D y ∈ C.source
    simp only [mem_univ, true_and]
  · ext Y
    change (Y ∈ C.target ∧ C.symm Y ∈ (Set.univ : Set (E2 × ℝ))) ↔ Y ∈ C.target
    simp only [mem_univ, and_true]
  · intro y
    rfl
  · intro Y
    exact referenceCompressedDiffeomorph_symm_apply a ha α hα hpos f (C.symm Y)
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨D y, ⟨mem_closedBall_zero_iff.mpr (hclosed y hy).1,
      (hclosed y hy).2⟩, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨D y, ⟨mem_closedBall_zero_iff.mpr
      (hclosed y (ball_subset_closedBall hy)).1, hopen y hy⟩, rfl⟩
  · intro X hX
    exact congrArg C (hcap X hX)
  · intro X hX
    have hXa : a ≤ referenceCapHeight a X := by
      simpa only [referenceCapPoint, heightCoordinates.apply_symm_apply] using
        (referenceCapPoint_cap_iff a ha X).mpr hX
    exact congrArg C (hcap X (hc₂a.le.trans hXa))
  · have hDsource : {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} ⊆
        B.chart.source := by
      intro y hy
      exact B.closedBall_subset_source (mem_closedBall_zero_iff.mpr hy.1.le)
    filter_upwards [hgerm, B.chart.open_source.mem_nhdsSet.mpr hDsource] with y heqy hy
    have hDy : D y ∈ C.source := hy.2
    exact ⟨hy, heqy ▸ hDy, congrArg C heqy⟩


theorem reference_ball_regions_of_side
    (A B : BallNeighborhoodChart E3 E3)
    (C : OpenPartialHomeomorph (E2 × ℝ) E3)
    (a : ℝ) (ha : a ∈ Set.Ioo (1 / 2 : ℝ) 1) (H η : ℝ)
    (hcentral : ∀ X : E2, ‖X‖ ≤ H →
      C (X, 0) = A.chart (referenceCapPoint a X))
    (hnegative : ∀ X : E2, ‖X‖ ≤ H → ∀ s : ℝ,
      -η < s → s < 0 → C (X, s) ∈ A.inside)
    (hclosed : B.closedRegion ⊆
      C '' (Metric.closedBall (0 : E2) H ×ˢ Set.Ioc (-η) 0))
    (hinside : B.inside ⊆
      C '' (Metric.closedBall (0 : E2) H ×ˢ Set.Ioo (-η) 0)) :
    B.closedRegion ⊆ A.closedRegion ∧ B.inside ⊆ A.inside := by
  constructor
  · intro y hy
    obtain ⟨⟨X, s⟩, hXs, rfl⟩ := hclosed hy
    have hX : ‖X‖ ≤ H := mem_closedBall_zero_iff.mp hXs.1
    by_cases hs : s = 0
    · subst s
      rw [hcentral X hX]
      exact ⟨referenceCapPoint a X,
        sphere_subset_closedBall (referenceCapPoint_mem_sphere a ha X), rfl⟩
    · exact (image_mono ball_subset_closedBall)
        (hnegative X hX s hXs.2.1 (lt_of_le_of_ne hXs.2.2 hs))
  · intro y hy
    obtain ⟨⟨X, s⟩, hXs, rfl⟩ := hinside hy
    exact hnegative X (mem_closedBall_zero_iff.mp hXs.1) s hXs.2.1 hXs.2.2

end PoincareConjecture.M25.Topology3D
