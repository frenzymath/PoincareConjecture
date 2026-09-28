import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurvatureLoss
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.OneDimensional














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_contDiff_geodesicCurvature_sq
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0) :
    ContDiff ℝ ∞ (fun x => intrinsicGeodesicCurvature N.metric N.connection radius x ^ 2) := by
  let gamma := intrinsicAnnulusBoundary radius
  let T := intrinsicBoundaryUnitTangent N.metric radius
  let V : ℝ → AnnulusCoordinates := fun x =>
    (intrinsicBoundarySpeed N.metric radius x)⁻¹ •
      rampHorizontalCovariantDerivative N.connection gamma T x
  have hgamma := m64Intrinsic_contDiff_boundary radius
  have hT := m64Intrinsic_contDiff_boundaryUnitTangent N hradius
  have hD := m64Intrinsic_contDiff_pullback N hgamma hT
  have hV : ContDiff ℝ ∞ V :=
    ((m64Intrinsic_contDiff_boundarySpeed N hradius).inv
      (fun x => (m64Intrinsic_boundarySpeed_pos N hradius x).ne')).smul hD
  have hg : ContDiff ℝ ∞ N.metric.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr N.metric.contDiffAt_euclideanCoefficients
  have h := ((hg.comp hgamma).clm_apply hV).clm_apply hV
  convert h using 1
  funext x
  apply Real.sq_sqrt
  by_cases hzero : V x = 0
  · change 0 ≤ N.metric.inner (gamma x) (V x) (V x)
    rw [hzero, map_zero]
  · exact (N.metric.pos (gamma x) (V x) hzero).le



theorem m64Intrinsic_contDiffAt_geodesicCurvature_of_pos
    (N : IntrinsicAnnulus) {radius x : ℝ} (hradius : radius ≠ 0)
    (hpos : 0 < intrinsicGeodesicCurvature N.metric N.connection radius x) :
    ContDiffAt ℝ ∞ (intrinsicGeodesicCurvature N.metric N.connection radius) x := by
  have h := (m64Intrinsic_contDiff_geodesicCurvature_sq N hradius).contDiffAt.sqrt
    (sq_pos_of_pos hpos).ne'
  convert! h using 1
  funext t
  exact (Real.sqrt_sq (show 0 ≤ intrinsicGeodesicCurvature N.metric N.connection radius t
    from Real.sqrt_nonneg _)).symm




theorem m64Intrinsic_exists_regular_curvature_threshold
    (N : IntrinsicAnnulus) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ alpha ∈ Ioo A B,
      intrinsicGeodesicCurvature N.metric N.connection 1 0 ≠ alpha ∧
      intrinsicGeodesicCurvature N.metric N.connection 1 rampPeriod ≠ alpha ∧
      {t | t ∈ Icc (0 : ℝ) rampPeriod ∧
        intrinsicGeodesicCurvature N.metric N.connection 1 t = alpha}.Finite ∧
      ∀ t ∈ Icc (0 : ℝ) rampPeriod,
        intrinsicGeodesicCurvature N.metric N.connection 1 t = alpha →
          deriv (intrinsicGeodesicCurvature N.metric N.connection 1) t ≠ 0 := by
  let k := intrinsicGeodesicCurvature N.metric N.connection 1
  let f : ℝ → ℝ := fun t => k t ^ 2
  have hf : ContDiff ℝ ∞ f :=
    m64Intrinsic_contDiff_geodesicCurvature_sq N (by norm_num : (1 : ℝ) ≠ 0)
  have hABsq : A ^ 2 < B ^ 2 := by nlinarith
  obtain ⟨c, hc, _, hregular⟩ :=
    Poincare.Analysis.exists_simultaneous_finite_regular_fibers
      (fun _ : Unit => f) (fun _ => (0 : ℝ)) (fun _ => rampPeriod)
      (fun _ => hf.continuous.continuousOn)
      (fun _ => (hf.differentiable (by simp)).differentiableOn) ∅ hABsq
  have hreg := hregular ()
  have hcpos : 0 < c := (sq_pos_of_pos hA).trans hc.1
  let alpha := Real.sqrt c
  have halpha : 0 < alpha := Real.sqrt_pos.mpr hcpos
  have hsquare : alpha ^ 2 = c := Real.sq_sqrt hcpos.le
  have hlow : A < alpha := by nlinarith [hc.1]
  have hupp : alpha < B := by nlinarith [hc.2]
  have hleft : k 0 ≠ alpha := by
    intro h
    exact hreg.1 (by change k 0 ^ 2 = c; rw [h, hsquare])
  have hright : k rampPeriod ≠ alpha := by
    intro h
    exact hreg.2.1 (by change k rampPeriod ^ 2 = c; rw [h, hsquare])
  refine ⟨alpha, ⟨hlow, hupp⟩, hleft, hright, ?_, ?_⟩
  · apply hreg.2.2.1.subset
    intro t ht
    have hkt : k t = alpha := ht.2
    exact ⟨ht.1, by change k t ^ 2 = c; rw [hkt, hsquare]⟩
  · intro t ht hkt
    change k t = alpha at hkt
    have ht' : t ∈ Ioo (0 : ℝ) rampPeriod :=
      ⟨lt_of_le_of_ne ht.1 (fun h => hleft (h ▸ hkt)),
        lt_of_le_of_ne ht.2 (fun h => hright (h ▸ hkt))⟩
    have hkpos : 0 < k t := by rw [hkt]; exact halpha
    have hkdiff : DifferentiableAt ℝ k t :=
      (m64Intrinsic_contDiffAt_geodesicCurvature_of_pos N
        (by norm_num : (1 : ℝ) ≠ 0) hkpos).differentiableAt (by simp)
    have hfd : deriv f t = 2 * k t * deriv k t := by
      simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using! (hkdiff.hasDerivAt.pow 2).deriv
    intro hzero
    change deriv k t = 0 at hzero
    apply hreg.2.2.2 t ht' (by change k t ^ 2 = c; rw [hkt, hsquare])
    rw [hfd, hzero, mul_zero]




theorem m64Intrinsic_exists_regular_curvature_cutoff
    (N : IntrinsicAnnulus) {delta r : ℝ} (hdelta : 0 < delta) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r) :
    ∃ alpha ∈ Ioo (100 * delta / r) (110 * delta / r),
      {t | t ∈ Icc (0 : ℝ) rampPeriod ∧
        intrinsicGeodesicCurvature N.metric N.connection 1 t = alpha}.Finite ∧
      (∀ t ∈ Icc (0 : ℝ) rampPeriod,
        intrinsicGeodesicCurvature N.metric N.connection 1 t = alpha →
          deriv (intrinsicGeodesicCurvature N.metric N.connection 1) t ≠ 0) ∧
      m64IntrinsicHighCurvatureLength N alpha <
        intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 := by
  obtain ⟨alpha, halpha, _, _, hfinite, hregular⟩ :=
    m64Intrinsic_exists_regular_curvature_threshold N
      (A := 100 * delta / r) (B := 110 * delta / r)
      (by positivity : 0 < 100 * delta / r)
      ((div_lt_div_iff_of_pos_right hr).mpr (by linarith))
  exact ⟨alpha, halpha, hfinite, hregular,
    m64Intrinsic_high_curvature_length_lt N hdelta hr hfirst hturn halpha.1.le⟩

end PoincareConjecture
