import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MeasurableNormalStrip
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurvatureLoss
import Mathlib.Topology.Order.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_global_measurable_normal_strip
    (K : ℝ) {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∀ N : IntrinsicAnnulus, N.GaussianCurvatureBound K →
      ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
        ∃ (u : ℝ × ℝ → AnnulusCoordinates) (height : ℝ → ℝ),
          ContDiff ℝ ∞ u ∧ Measurable height ∧
          (∀ s, u (s, 0) = intrinsicAnnulusBoundary 1 s) ∧
          (∀ s, 0 < height s ∧ height s ≤ R ∧
            (∀ t ∈ Ioo (0 : ℝ) (height s),
              1 < ‖u (s, t)‖ ∧ ‖u (s, t)‖ < 2) ∧
            u (s, height s) ∈ standardAnnulusDomain ∧
            (height s = R ∨ ‖u (s, height s)‖ = 1 ∨
              ‖u (s, height s)‖ = 2)) ∧
          ∀ a ∈ Icc (0 : ℝ) rampPeriod, ∃ S I : Set ℝ, IsOpen S ∧ IsOpen I ∧ a ∈ S ∧
            Icc (0 : ℝ) (height a) ⊆ I ∧
            (∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I) ∧
            ∀ t ∈ Icc (0 : ℝ) (height a),
              (∀ v : ℝ × ℝ,
                (1 - delta) ^ 2 *
                    ((intrinsicBoundarySpeed N.metric 1 a) ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
                  N.metric.inner (u (a, t))
                    (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) ∧
              Function.Injective (fderiv ℝ u (a, t)) ∧
              (1 - delta) ^ 2 * intrinsicBoundarySpeed N.metric 1 a ≤
                N.metric.pullbackVolumeDensity
                  (fun z : AnnulusCoordinates => u (z 0, z 1)) !₂[a, t] := by
  intro N hK
  let k : ℝ → ℝ :=
    intrinsicGeodesicCurvature N.metric N.connection 1
  have hkcont : Continuous k :=
    (m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0))
  have hbound : BddAbove (k '' Icc (0 : ℝ) rampPeriod) :=
    isCompact_Icc.bddAbove_image hkcont.continuousOn
  obtain ⟨A, hA⟩ := hbound
  let alpha := max A 0
  have halpha : 0 ≤ alpha := le_max_right _ _
  have hka (a : ℝ) (ha : a ∈ Icc (0 : ℝ) rampPeriod) : k a ≤ alpha :=
    (hA ⟨a, ha, rfl⟩).trans (le_max_left _ _)
  obtain ⟨R, hR, hRsmall, hstrip⟩ :=
    m64Intrinsic_exists_uniform_measurable_normal_strip K hdelta hdelta1 halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  obtain ⟨u, height, hu, hheight, hboundary, hcontact, hlocal⟩ := hstrip N hK
  refine ⟨u, height, hu, hheight, hboundary, hcontact, ?_⟩
  intro a ha_period
  obtain ⟨S, I, hS, hI, ha, hsub, hgeo, hmetric⟩ := hlocal a
    (show intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha from by
      simpa [k] using hka a ha_period)
  exact ⟨S, I, hS, hI, ha, hsub, hgeo, hmetric⟩

end PoincareConjecture
