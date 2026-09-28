import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CyclicRetainedStripLosses
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointProjection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_comparison_of_cyclic_retained_strip
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e) {height : ℝ → ℝ} (hh : Measurable height)
    (hheight_nonneg : ∀ a, 0 ≤ height a)
    {delta r alpha R rho kappa : ℝ}
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / r ≤ alpha)
    (hR : 0 < R) (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hangle : kappa * rho ≤ Real.pi / 4)
    (hrhoSmall : rho ≤ 3 * r / (1600 * delta))
    (harea : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * R * (r / 10))
    (hray : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)))
    (hfocus : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      ∀ b ∈ Ico (0 : ℝ) rampPeriod,
        intrinsicGeodesicCurvature N.metric N.connection 1 b ≤ alpha → a < b →
        (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b),
          e !₂[a, t] = e !₂[b, s]) →
        (Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) ∨
        (Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 b (a + rampPeriod)))
    (hmetric : ∀ x : AnnulusCoordinates, x 0 ∈ Ico (0 : ℝ) rampPeriod →
      intrinsicGeodesicCurvature N.metric N.connection 1 (x 0) ≤ alpha →
      x 1 ∈ Icc 0 (height (x 0)) → ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v)
            (mfderiv (𝓡 2) (𝓡 2) e x v))
    (himage : ∀ x : AnnulusCoordinates, x 0 ∈ Ico (0 : ℝ) rampPeriod →
      intrinsicGeodesicCurvature N.metric N.connection 1 (x 0) ≤ alpha →
      x 1 ∈ Icc 0 (height (x 0)) → e x ∈ standardAnnulusDomain)
    (hendpoint_reg : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      height a < R →
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, height a]))
    (houter : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      height a < R → ‖e !₂[a, height a]‖ = 2) :
    (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod <
      intrinsicBoundaryLength N.metric 2 0 rampPeriod := by
  obtain ⟨E, hE, hEsub, hfocusLoss, hS, hZ, hinj, _, hlong, hshort⟩ :=
    m64Intrinsic_exists_cyclic_retained_strip_three_losses N e
      (he.differentiable (by simp)) hh
      hdelta hdeltaSmall hr hfirst hturn halpha hR hrho hkappa hangle hrhoSmall harea
      hray hfocus hmetric himage
  let Z : Set ℝ :=
    ((Ico (0 : ℝ) rampPeriod ∩
      {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}) \ E) ∩
        {s | height s < R}
  have hZeq : Z = ((Ico (0 : ℝ) rampPeriod ∩
      {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}) \ E) ∩
        {s | height s < R} := rfl
  have hZsub : Z ⊆ Ico (0 : ℝ) rampPeriod := by
    intro a ha
    exact ha.1.1.1
  have hZend : ∀ a ∈ Z, ‖e !₂[a, height a]‖ = 2 := by
    intro a ha
    exact houter a ha.1.1.1 ha.1.1.2 ha.2
  have hZinj : InjOn (fun a => e !₂[a, height a]) Z := by
    intro a ha b hb hab
    have hpair : !₂[a, height a] = !₂[b, height b] := by
      apply hinj
      · exact ⟨ha.1, ⟨hheight_nonneg a, le_rfl⟩⟩
      · exact ⟨hb.1, ⟨hheight_nonneg b, le_rfl⟩⟩
      · exact hab
    have hcoord := congrArg (fun z : AnnulusCoordinates => z 0) hpair
    simpa only [Matrix.cons_val_zero] using hcoord
  have hZreg : ∀ a ∈ Z,
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, height a]) := by
    intro a ha
    exact hendpoint_reg a ha.1.1.1 ha.1.1.2 ha.2
  have hZbound : ∀ a ∈ Z, ∀ v : AnnulusCoordinates,
      (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 a ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[a, height a])
          (fderiv ℝ e !₂[a, height a] v) (fderiv ℝ e !₂[a, height a] v) := by
    intro a ha v
    convert hmetric !₂[a, height a] ha.1.1.1 ha.1.1.2
        ⟨hheight_nonneg a, le_rfl⟩ v using 1 <;>
      simp only [mfderiv_eq_fderiv, Matrix.cons_val_zero]
    all_goals rfl
  have hproj := m64Intrinsic_endpoint_projection_length_le N e
    he hh hZ hZsub hZinj hZreg hZend
    (sub_nonneg.mpr (by linarith)) hZbound
  have hproj' : (1 - delta) *
      (∫ s in Z, intrinsicBoundarySpeed N.metric 1 s) ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod := by
    simpa only [hZeq] using hproj
  have hshort' : (3 / 4 : ℝ) *
      intrinsicBoundaryLength N.metric 1 0 rampPeriod <
      (1 - delta) * (∫ s in Z, intrinsicBoundarySpeed N.metric 1 s) := by
    simpa only [Z] using hshort
  exact hshort'.trans_le hproj'

end PoincareConjecture
