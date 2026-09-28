import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_RetainedNormalGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RetainedComparison
















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_exists_actual_retained_comparison
    (N : IntrinsicAnnulus) {delta r K : ℝ}
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hr : 0 < r) (hK : N.GaussianCurvatureBound K)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r) :
    ∃ mu : ℝ, 0 < mu ∧
      (intrinsicAnnulusArea N.metric < mu →
        (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod <
          intrinsicBoundaryLength N.metric 2 0 rampPeriod) := by
  have hdelta1 : delta < 1 := by linarith
  let alpha : ℝ := 100 * delta / r
  have halpha : 100 * delta / r ≤ alpha := le_rfl
  obtain ⟨R, hR, hRsmall, e, height, he, hh, hheight, hray, hglobal,
      hmetric, himage, houter, hendreg⟩ :=
    m64Intrinsic_exists_retained_normal_geometry N K hK hdelta hdelta1
  let kappa : ℝ := 1
  let rho : ℝ := min (Real.pi / 8) (3 * r / (800 * delta))
  have hkappa : 0 < kappa := by simp [kappa]
  have hrho : 0 < rho := by
    dsimp [rho]
    exact lt_min (by positivity) (by positivity)
  have hangle : kappa * rho ≤ Real.pi / 4 := by
    have hrho_pi : rho ≤ Real.pi / 8 := min_le_left _ _
    dsimp [kappa]
    linarith
  have hrhoSmall : rho ≤ 3 * r / (800 * delta) := min_le_right _ _
  let mu : ℝ := (1 - delta) ^ 2 * R * (r / 10)
  have hmu : 0 < mu := by
    dsimp [mu]
    positivity
  refine ⟨mu, hmu, ?_⟩
  intro harea
  have harea' : intrinsicAnnulusArea N.metric <
      (1 - delta) ^ 2 * R * (r / 10) := by
    simpa only [mu] using harea
  have hfocus : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      ∀ b ∈ Ico (0 : ℝ) rampPeriod,
        intrinsicGeodesicCurvature N.metric N.connection 1 b ≤ alpha → a < b →
        (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b),
          e !₂[a, t] = e !₂[b, s]) →
        Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
    intro a ha hka b hb hkb hab hmeet
    exact m64Intrinsic_retained_focusing_of_global_injective N hglobal
      a ha hka b hb hkb hab hmeet
  have hmetric' : ∀ x : AnnulusCoordinates,
      x 0 ∈ Ico (0 : ℝ) rampPeriod →
      intrinsicGeodesicCurvature N.metric N.connection 1 (x 0) ≤ alpha →
      x 1 ∈ Icc 0 (height (x 0)) → ∀ v : AnnulusCoordinates,
      (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e x)
          (mfderiv (𝓡 2) (𝓡 2) e x v)
          (mfderiv (𝓡 2) (𝓡 2) e x v) := by
    intro x hx0 hxk hx1 v
    convert hmetric x hx0 hx1 v using 1
    all_goals simp only [mfderiv_eq_fderiv]
    all_goals rfl
  have hendreg' : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
      height a < R →
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, height a]) := by
    intro a ha hka haR
    rw [mfderiv_eq_fderiv]
    change Function.Injective (fderiv ℝ e !₂[a, height a])
    exact hendreg a ha haR
  exact m64Intrinsic_comparison_of_retained_strip N e he hh
    (fun a => (hheight a).1.le) hdelta hdeltaSmall hr hfirst hturn halpha
    hR hrho hkappa hangle hrhoSmall harea'
    (fun a ha _ => hray a ha) hfocus hmetric'
    (fun x hx0 _ hx1 => himage x hx0 hx1) hendreg'
    (fun a ha _ haR => houter a ha haR)

end PoincareConjecture
