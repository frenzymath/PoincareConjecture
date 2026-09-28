import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.CurveDistance
import PoincareConjecture.Proofs.M58.Mathlib.CompactRiemannianBallBundle












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem m64_c2_sweep_fixed_metric_bounds
    {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (g : RiemannianMetric n M) :
    ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ x ∈ Icc 0 curvePeriod, ∀ t ∈ Icc a b,
        g.tangentNorm (c x t) (curveVelocity (fun y => c y t) x) ≤ S) ∧
      (∀ x ∈ Icc 0 curvePeriod, ∀ t ∈ Icc a b,
        g.tangentNorm (c x t) (m62CurvatureVector F c t x) ≤ H) := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hvelocity : ContinuousOn (fun z : ℝ × ℝ =>
      g.tangentNorm (c z.1 z.2) (curveVelocity (fun y => c y z.2) z.1))
      (univ ×ˢ Icc a b) :=
    Proofs.M58.continuous_bundle_norm.comp_continuousOn hc.velocity_continuous
  have hcurvature : ContinuousOn (fun z : ℝ × ℝ =>
      g.tangentNorm (c z.1 z.2) (m62CurvatureVector F c z.2 z.1))
      (univ ×ˢ Icc a b) :=
    Proofs.M58.continuous_bundle_norm.comp_continuousOn hc.curvature_continuous
  have hsub : Icc 0 curvePeriod ×ˢ Icc a b ⊆ univ ×ˢ Icc a b :=
    prod_mono (subset_univ _) Subset.rfl
  obtain ⟨S, hS⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (hvelocity.mono hsub)
  obtain ⟨H, hH⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (hcurvature.mono hsub)
  refine ⟨max S 0, max H 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro x hx t ht
    exact (hS ⟨(x, t), ⟨hx, ht⟩, rfl⟩).trans (le_max_left _ _)
  · intro x hx t ht
    exact (hH ⟨(x, t), ⟨hx, ht⟩, rfl⟩).trans (le_max_left _ _)



theorem m64_c2_time_slice_contMDiffOn
    {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (x : ℝ) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun t => c x t) (Ioo a b) := by
  have hpair : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) 1 (fun t : ℝ => (x, t)) :=
    contMDiff_iff_contDiff.mpr (contDiff_const.prodMk contDiff_id)
  apply hc.joint_c1.comp hpair.contMDiffOn
  intro t ht
  change (x, t) ∈ univ ×ˢ interior (Icc a b)
  rw [interior_Icc]
  exact ⟨mem_univ _, ht⟩




theorem m64_c2_time_slice_edist [T2Space M]
    {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (g : RiemannianMetric n M)
    {x H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ t ∈ Icc a b, g.tangentNorm (c x t) (m62CurvatureVector F c t x) ≤ H)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    g.edist (c x s) (c x t) ≤ ENNReal.ofReal H * ENNReal.ofReal |s - t| := by
  apply m64_curve_edist_le_speed_closed g hH (m64_c2_time_slice_contMDiffOn hc x)
    (hc.continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨mem_univ _, hu⟩)) ?_ s hs t ht
  intro u hu
  rw [hc.equation u (by simpa only [interior_Icc] using hu) x]
  exact hbound u ⟨hu.1.le, hu.2.le⟩



theorem m64_c2_spatial_slice_edist [T2Space M]
    {F : RicciFlow n M (Icc a b)} {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) (g : RiemannianMetric n M)
    {t S : ℝ} (ht : t ∈ Icc a b) (hS : 0 ≤ S)
    (hbound : ∀ x ∈ Icc 0 curvePeriod,
      g.tangentNorm (c x t) (curveVelocity (fun y => c y t) x) ≤ S)
    {x y : ℝ} (hx : x ∈ Icc 0 curvePeriod) (hy : y ∈ Icc 0 curvePeriod) :
    g.edist (c x t) (c y t) ≤ ENNReal.ofReal S * ENNReal.ofReal |x - y| := by
  have hreg : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c x t) :=
    (hc.spatial_regular t ht).of_le (by norm_num)
  exact m64_curve_edist_le_speed_closed g hS hreg.contMDiffOn
    hreg.continuous.continuousOn (fun x hx => hbound x ⟨hx.1.le, hx.2.le⟩) x hx y hy

end PoincareConjecture
