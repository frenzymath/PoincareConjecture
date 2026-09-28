import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Density

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

theorem m64Intrinsic_det_lower_of_quadratic_lower
    {a b d A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hbound : ∀ x y : ℝ, A * x ^ 2 + D * y ^ 2 ≤
      a * x ^ 2 + 2 * b * x * y + d * y ^ 2) :
    A * D ≤ a * d - b ^ 2 := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![a - A, b; b, d - D]
  have hM : M.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [M, Matrix.conjTranspose_apply]
    · intro z
      have h := hbound (z 0) (z 1)
      simp [M, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      nlinarith only [h]
  have hdet := hM.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  change 0 ≤ (a - A) * (d - D) - b * b at hdet
  have ha : A ≤ a := by simpa using hbound 1 0
  have hd : D ≤ d := by simpa using hbound 0 1
  nlinarith [mul_nonneg hA (sub_nonneg.mpr hd), mul_nonneg hD (sub_nonneg.mpr ha)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_pullbackDensity_lower
    (G : RiemannianMetric 2 AnnulusCoordinates)
    (e : AnnulusCoordinates → AnnulusCoordinates) (x : AnnulusCoordinates)
    {c speed : ℝ}
    (hbound : ∀ v : AnnulusCoordinates,
      c ^ 2 * (speed ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        G.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v)) :
    c ^ 2 * speed ≤ G.pullbackVolumeDensity e x := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let L := mfderiv (𝓡 2) (𝓡 2) e x
  let a := G.inner (e x) (L (b 0)) (L (b 0))
  let d := G.inner (e x) (L (b 1)) (L (b 1))
  let k := G.inner (e x) (L (b 0)) (L (b 1))
  have hsymm : G.inner (e x) (L (b 1)) (L (b 0)) = k := G.symm _ _ _
  have hquad (s t : ℝ) : c ^ 2 * speed ^ 2 * s ^ 2 + c ^ 2 * t ^ 2 ≤
      a * s ^ 2 + 2 * k * s * t + d * t ^ 2 := by
    have h := hbound (s • b 0 + t • b 1)
    have hz0 : (s • b 0 + t • b 1) 0 = s := by simp [b]
    have hz1 : (s • b 0 + t • b 1) 1 = t := by simp [b]
    rw [hz0, hz1] at h
    change c ^ 2 * (speed ^ 2 * s ^ 2 + t ^ 2) ≤
      G.inner (e x) (L (s • b 0 + t • b 1)) (L (s • b 0 + t • b 1)) at h
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hsymm] at h
    change c ^ 2 * (speed ^ 2 * s ^ 2 + t ^ 2) ≤
      s * (s * a + t * k) + t * (s * k + t * d) at h
    nlinarith only [h]
  have hdet := m64Intrinsic_det_lower_of_quadratic_lower
    (mul_nonneg (sq_nonneg c) (sq_nonneg speed)) (sq_nonneg c) hquad
  unfold RiemannianMetric.pullbackVolumeDensity
  apply Real.le_sqrt_of_sq_le
  rw [Matrix.det_fin_two]
  change (c ^ 2 * speed) ^ 2 ≤ a * d - k * G.inner (e x) (L (b 1)) (L (b 0))
  rw [hsymm]
  nlinarith only [hdet]

theorem m64Intrinsic_chart_area_lower
    (G : RiemannianMetric 2 AnnulusCoordinates)
    (e : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {S : Set AnnulusCoordinates} (hS : MeasurableSet S) (hsource : S ⊆ e.source)
    {c : ℝ} (speed : ℝ → ℝ)
    (hbound : ∀ x ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (speed (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        G.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v))
    (himage : e '' S ⊆ standardAnnulusDomain) :
    (∫⁻ x in S, ENNReal.ofReal (c ^ 2 * speed (x 0))) ≤
      ENNReal.ofReal (intrinsicAnnulusArea G) := by
  have hformula := G.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei hS hsource
  have harea := m64Intrinsic_region_volume_le_area G himage
  calc
    _ ≤ ∫⁻ x in S, ENNReal.ofReal (G.pullbackVolumeDensity e x) := by
      apply setLIntegral_mono' hS
      intro x hx
      exact ENNReal.ofReal_le_ofReal (m64Intrinsic_pullbackDensity_lower G e x (hbound x hx))
    _ = G.volumeMeasure (e '' S) := hformula.symm
    _ ≤ ENNReal.ofReal (intrinsicAnnulusArea G) := by
      rw [← ENNReal.ofReal_toReal harea.1.ne]
      exact ENNReal.ofReal_le_ofReal harea.2

end PoincareConjecture
