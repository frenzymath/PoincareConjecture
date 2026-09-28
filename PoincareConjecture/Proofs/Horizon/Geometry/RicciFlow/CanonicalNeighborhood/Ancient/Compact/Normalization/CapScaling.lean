import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.QuotientHomothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.HessianTensorial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.ScalarGradientTransport
import Mathlib.Data.Real.Pointwise

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology Pointwise

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem rescaledMetric_intrinsicEDist (g : RiemannianMetric 3 M)
    (c : ℝ) (hc : 0 < c) (X : Set M) (x y : M) :
    intrinsicEDist (rescaledMetric g c hc) X x y =
      ENNReal.ofReal (Real.sqrt c) * intrinsicEDist g X x y := by
  have hne : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  unfold intrinsicEDist
  have heq : {L | ∃ γ : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc (0 : ℝ) 1) ∧
        γ 0 = x ∧ γ 1 = y ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ X ∧
          L = (rescaledMetric g c hc).pathELength γ 0 1} =
      (fun L => ENNReal.ofReal (Real.sqrt c) * L) ''
        {L | ∃ γ : ℝ → M,
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc (0 : ℝ) 1) ∧
            γ 0 = x ∧ γ 1 = y ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ X ∧
              L = g.pathELength γ 0 1} := by
    ext L
    constructor
    · rintro ⟨γ, hγ, hx, hy, hX, rfl⟩
      exact ⟨g.pathELength γ 0 1, ⟨γ, hγ, hx, hy, hX, rfl⟩,
        (rescaledMetric_pathELength g c hc γ 0 1).symm⟩
    · rintro ⟨L, ⟨γ, hγ, hx, hy, hX, rfl⟩, rfl⟩
      exact ⟨γ, hγ, hx, hy, hX, (rescaledMetric_pathELength g c hc γ 0 1).symm⟩
  rw [heq, sInf_image, sInf_eq_iInf,
    ENNReal.mul_iInf_of_ne hne ENNReal.ofReal_ne_top]
  congr 1
  funext L
  rw [ENNReal.mul_iInf_of_ne hne ENNReal.ofReal_ne_top]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem rescaledMetric_intrinsicDiameter (g : RiemannianMetric 3 M)
    (c : ℝ) (hc : 0 < c) (X : Set M) :
    intrinsicDiameter (rescaledMetric g c hc) X =
      ENNReal.ofReal (Real.sqrt c) * intrinsicDiameter g X := by
  simp only [intrinsicDiameter, rescaledMetric_intrinsicEDist, sSup_range,
    ENNReal.mul_iSup]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem rescaledMetric_scalarCurvatureSupOn (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) (X : Set M) :
    scalarCurvatureSupOn (rescaledMetric g c hc)
      (rescaledMetric_connection g D c hc) X = c⁻¹ * scalarCurvatureSupOn g D X := by
  simp only [scalarCurvatureSupOn, rescaledMetric_scalarCurvature]
  simpa only [Set.smul_set_range, smul_eq_mul] using
    Real.sSup_smul_of_nonneg (inv_nonneg.mpr hc.le)
      (Set.range (fun z : X => D.scalarCurvature z))

omit [T2Space M] in
theorem rescaledMetric_calibratedMetricVolume (g : RiemannianMetric 3 M)
    (c : ℝ) (hc : 0 < c) (X : Set M) :
    calibratedMetricVolume (rescaledMetric g c hc) X =
      ENNReal.ofReal (Real.sqrt c) ^ 3 * calibratedMetricVolume g X := by
  change euclideanVolumeCalibration 3 * (rescaledMetric g c hc).hausdorffVolume X =
    ENNReal.ofReal (Real.sqrt c) ^ 3 * (euclideanVolumeCalibration 3 * g.hausdorffVolume X)
  rw [rescaledMetric_hausdorffVolume]
  ac_rfl

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem rescaledMetric_laplacian (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) (f : M → ℝ) (x : M)
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ) ∞ f x) :
    (rescaledMetric_connection g D c hc).laplacian f x = c⁻¹ * D.laplacian f x := by
  let B := M48ScalarCalculus.hessianBilin D f x hf
  have hB (v w : TangentSpace (𝓡 3) x) : B v w = D.hessian f x v w :=
    M48ScalarCalculus.hessianBilin_apply_eq_hessian D f x hf v w
  change (∑ i, D.hessian f x _ _) = c⁻¹ * ∑ i, D.hessian f x _ _
  simp_rw [← hB]
  exact rescaledMetric_bilinear_trace g c hc x (ContinuousLinearMap.toLinearMap₁₂ B)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem rescaledMetric_scalarEvolution (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) (x : M) :
    (rescaledMetric_connection g D c hc).laplacian
        (rescaledMetric_connection g D c hc).scalarCurvature x +
        2 * (rescaledMetric_connection g D c hc).ricciNormSq x =
      c⁻¹ ^ 2 * (D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x) := by
  have hR : (rescaledMetric_connection g D c hc).scalarCurvature =
      fun y => c⁻¹ * D.scalarCurvature y := funext (rescaledMetric_scalarCurvature g D c hc)
  rw [hR, LeviCivitaData.laplacian_const_mul,
    rescaledMetric_laplacian g D c hc _ x (M48.scalarCurvature_smooth D).contMDiffAt,
    rescaledMetric_ricciNormSq g D D.intrinsicCurvatureTensorCalculus c hc]
  ring

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem rescaledMetric_scalarGradientNorm (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) (x : M) :
    scalarGradientNorm (rescaledMetric g c hc) (rescaledMetric_connection g D c hc) x =
      (c⁻¹ * (Real.sqrt c)⁻¹) * scalarGradientNorm g D x := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hR : (rescaledMetric_connection g D c hc).scalarCurvature =
      fun y => c⁻¹ * D.scalarCurvature y := funext (rescaledMetric_scalarCurvature g D c hc)
  unfold scalarGradientNorm
  rw [hR]
  have heq : Set.range (fun v :
      {v : TangentSpace (𝓡 3) x // (rescaledMetric g c hc).inner x v v = 1} =>
        |mvfderiv (𝓡 3) (fun y => c⁻¹ * D.scalarCurvature y) x v.1|) =
      (c⁻¹ * (Real.sqrt c)⁻¹) • Set.range (fun v :
        {v : TangentSpace (𝓡 3) x // g.inner x v v = 1} =>
          |mvfderiv (𝓡 3) D.scalarCurvature x v.1|) := by
    rw [Set.smul_set_range]
    ext a
    constructor
    · rintro ⟨v, rfl⟩
      have hv : g.inner x (Real.sqrt c • v.1) (Real.sqrt c • v.1) = 1 := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        rw [← mul_assoc, hsq]
        exact v.2
      refine ⟨⟨Real.sqrt c • v.1, hv⟩, ?_⟩
      change (c⁻¹ * (Real.sqrt c)⁻¹) *
        |mvfderiv (𝓡 3) D.scalarCurvature x (Real.sqrt c • v.1)| =
        |mvfderiv (𝓡 3) (fun y => c⁻¹ * D.scalarCurvature y) x v.1|
      rw [mvfderiv_const_mul]
      simp only [smul_eq_mul, mvfderiv, map_smul, abs_mul,
        abs_of_pos hs, abs_of_pos (inv_pos.mpr hc)]
      field_simp
    · rintro ⟨v, rfl⟩
      have hv : (rescaledMetric g c hc).inner x
          ((Real.sqrt c)⁻¹ • v.1) ((Real.sqrt c)⁻¹ • v.1) = 1 := by
        rw [rescaledMetric_inner_normalized, v.2]
      refine ⟨⟨(Real.sqrt c)⁻¹ • v.1, hv⟩, ?_⟩
      change |mvfderiv (𝓡 3) (fun y => c⁻¹ * D.scalarCurvature y) x
        ((Real.sqrt c)⁻¹ • v.1)| =
        (c⁻¹ * (Real.sqrt c)⁻¹) * |mvfderiv (𝓡 3) D.scalarCurvature x v.1|
      rw [mvfderiv_const_mul]
      simp only [mvfderiv, map_smul, smul_eq_mul, abs_mul,
        abs_of_pos (inv_pos.mpr hs), abs_of_pos (inv_pos.mpr hc)]
      ring
  rw [heq, Real.sSup_smul_of_nonneg (mul_nonneg (inv_nonneg.mpr hc.le)
    (inv_nonneg.mpr hs.le)), smul_eq_mul]

end PoincareConjecture
