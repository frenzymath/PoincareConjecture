import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Analysis.GramScaling
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.ChartDensitySmooth
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.GramNormalization
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Evolution.MetricTrace

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/ScaledJacobianComparison.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Actual metric comparison and the dimensional Jacobian factor

Morgan-Tian Definition 2.16, p. 30, and Theorem 13.2, pp. 332-333,
give metric comparison at inverse-squared length scale. Normalizing the
actual source Gram matrix makes its volume consequence explicit, with
length to the dimension, as required in Lemma 17.12, p. 410.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareMT.SurgeryVolume

-- Normalization retains the selected metric's dependent tangent norm.
set_option backward.isDefEq.respectTransparency false in
/-- Paired metric error controls both actual Gram densities with the
dimensional scale (MT Definition 2.16, p. 30; Lemma 17.12, p. 410). -/
theorem pullbackJacobian_comparison_of_bilinear_error
    {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    (g₀ : RiemannianMetric n M) (g₁ : RiemannianMetric n N)
    (f₀ : EuclideanSpace ℝ (Fin n) → M) (f₁ : EuclideanSpace ℝ (Fin n) → N)
    (x : EuclideanSpace ℝ (Fin n)) {h eta : ℝ} (hh : 0 < h)
    (heta : ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |A i j - if i = j then 1 else 0| ≤ eta) →
        (1 / 2 : ℝ) ≤ Real.sqrt A.det ∧ Real.sqrt A.det ≤ 2)
    (hD : (mfderiv (𝓡 n) (𝓡 n) f₀ x).IsInvertible)
    (herror : ∀ v w : EuclideanSpace ℝ (Fin n),
      |h⁻¹ ^ 2 * SurgeryVolume.Measure.pullbackMetricForm g₁ f₁ x v w -
        SurgeryVolume.Measure.pullbackMetricForm g₀ f₀ x v w| ≤
        eta * g₀.tangentNorm (f₀ x) (mfderiv (𝓡 n) (𝓡 n) f₀ x v) *
          g₀.tangentNorm (f₀ x) (mfderiv (𝓡 n) (𝓡 n) f₀ x w)) :
    (h ^ n / 2) * SurgeryVolume.Measure.pullbackJacobian g₀ f₀ x ≤ SurgeryVolume.Measure.pullbackJacobian g₁ f₁ x ∧
      SurgeryVolume.Measure.pullbackJacobian g₁ f₁ x ≤ (2 * h ^ n) * SurgeryVolume.Measure.pullbackJacobian g₀ f₀ x := by
  obtain ⟨C, hC⟩ := SurgeryVolume.Measure.exists_pullback_source_normalization g₀ hD
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let G : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => SurgeryVolume.Measure.pullbackMetricForm g₁ f₁ x (C (b i)) (C (b j))
  let A : Matrix (Fin n) (Fin n) ℝ := h⁻¹ ^ 2 • G
  have hnorm (i : Fin n) :
      g₀.tangentNorm (f₀ x) (mfderiv (𝓡 n) (𝓡 n) f₀ x (C (b i))) = 1 := by
    rw [hC, SurgeryVolume.Measure.metricCoordinates_tangentNorm]
    exact b.norm_eq_one i
  have hgram (i j : Fin n) :
      SurgeryVolume.Measure.pullbackMetricForm g₀ f₀ x (C (b i)) (C (b j)) =
        if i = j then 1 else 0 := by
    have hp : g₀.inner (f₀ x)
        (mfderiv (𝓡 n) (𝓡 n) f₀ x (C (b i)))
        (mfderiv (𝓡 n) (𝓡 n) f₀ x (C (b j))) =
          if i = j then 1 else 0 := by
      rw [hC, hC]
      exact SurgeryVolume.Measure.metricCoordinates_basis_inner g₀ (f₀ x) i j
    simpa only [SurgeryVolume.Measure.pullbackMetricForm, ContinuousLinearMap.bilinearComp_apply] using! hp
  have hA := heta A (fun i j => by
    have he := herror (C (b i)) (C (b j))
    simpa only [A, G, Matrix.smul_apply, smul_eq_mul, hgram, hnorm, mul_one] using! he)
  have hJ₀ : SurgeryVolume.Measure.pullbackJacobian g₀ f₀ x * C.toLinearMap.normDet = 1 := by
    have hI : (fun i j : Fin n => SurgeryVolume.Measure.pullbackMetricForm g₀ f₀ x
        (C (b i)) (C (b j))) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      rw [hgram, Matrix.one_apply]
    have hsource : Real.sqrt (Matrix.det (fun i j : Fin n =>
        SurgeryVolume.Measure.pullbackMetricForm g₀ f₀ x (C (b i)) (C (b j)))) =
          SurgeryVolume.Measure.pullbackJacobian g₀ f₀ x * C.toLinearMap.normDet :=
      SurgeryVolume.Measure.sqrt_det_pullbackMetric_change_source g₀ f₀ x C.toLinearMap
    rw [hI, Matrix.det_one, Real.sqrt_one] at hsource
    exact hsource.symm
  have hscale : Real.sqrt A.det * h ^ n =
      SurgeryVolume.Measure.pullbackJacobian g₁ f₁ x * C.toLinearMap.normDet := by
    dsimp only [A]
    rw [Matrix.sqrt_det_smul_sq G (inv_nonneg.mpr hh.le), Fintype.card_fin]
    change (h⁻¹ ^ n * Real.sqrt G.det) * h ^ n = _
    rw [show Real.sqrt G.det = SurgeryVolume.Measure.pullbackJacobian g₁ f₁ x *
        C.toLinearMap.normDet from
      SurgeryVolume.Measure.sqrt_det_pullbackMetric_change_source g₁ f₁ x C.toLinearMap]
    rw [inv_pow]
    field_simp
  have hk := SurgeryVolume.Measure.source_normalization_normDet_pos C
  constructor
  · apply (mul_le_mul_iff_left₀ hk).mp
    have hl := mul_le_mul_of_nonneg_right hA.1 (pow_nonneg hh.le n)
    rw [hscale] at hl
    simpa only [mul_assoc, hJ₀, mul_one, one_div, div_eq_mul_inv, mul_comm] using hl
  · apply (mul_le_mul_iff_left₀ hk).mp
    have hu := mul_le_mul_of_nonneg_right hA.2 (pow_nonneg hh.le n)
    rw [hscale] at hu
    simpa only [mul_assoc, hJ₀, mul_one] using hu

end PoincareMT.SurgeryVolume
