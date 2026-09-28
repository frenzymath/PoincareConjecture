import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeReference
import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeImage

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M34

noncomputable def capBallVolumeCoefficient (C : ℝ) : ℝ :=
  ((100 * C)⁻¹) ^ 3 / (8 * C * (2 * C) ^ 3)

theorem capBallVolumeCoefficient_pos {C : ℝ} (hC : 0 < C) :
    0 < capBallVolumeCoefficient C := by
  unfold capBallVolumeCoefficient
  positivity

end PoincareConjecture.M34

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [MeasurableSpace X] [BorelSpace M] [BorelSpace X]
  [T3Space M] [T3Space X] [SecondCountableTopology M] [SecondCountableTopology X]
  [ConnectedSpace M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem normalized_image_core_ball_volume_lower
    {C : ℝ} (hC1 : 1 ≤ C) (hC : N.cap_constant ≤ C)
    (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ v : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x v v)
    {o : M} (ho : o ∈ N.carrier) (hnormal : N.connection.scalarCurvature o = 1)
    (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target)
    (hsource : N.carrier ⊆ e.source)
    (hupper : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤ 2 * g.tangentNorm x v)
    (hlower : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ 2 * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v))
    {y : M} (hy : y ∈ N.core) {r : ℝ} (hr : 0 < r)
    (hnew : scalarCurvatureSupOn h D (h.ball (e y) r) = r⁻¹ ^ 2)
    (hscalar : ∀ x ∈ h.ball (e y) r, (2 * C)⁻¹ ≤ D.scalarCurvature x ∧
      D.scalarCurvature x ≤ 2 * C) :
    ENNReal.ofReal (M34.capBallVolumeCoefficient C * r ^ 3) ≤
      calibratedMetricVolume h (h.ball (e y) r) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hhC : (100 * C)⁻¹ ≤ C⁻¹ :=
    (inv_le_inv₀ (by positivity) hCpos).mpr (by linarith)
  have hh0 := hhC.trans (N.core_radius_bounds_of_normalized_base ho hnormal hC hC1 hy).1
  have hball : g.ball y ((100 * C)⁻¹) ⊆ e.source := by
    intro x hx
    apply hsource
    apply N.core_ball_subset y hy
    exact subset_closure (hx.trans_le (ENNReal.ofReal_le_ofReal hh0))
  have hradius := h.scalar_normalized_radius_bounds (B := 2 * C) D (e y) hr
    (by linarith) hnew hscalar
  have hsmall : 2 * (100 * C)⁻¹ ≤ (2 * C)⁻¹ := by
    simp only [mul_inv_rev]
    norm_num
    linarith [inv_pos.mpr hCpos]
  have hvol := M34.calibrated_ball_volume_le_mul_of_tangent_bounds g h e hf hi
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)
    hupper hlower hball (hsmall.trans hradius.1)
  have hreference := N.reference_core_ball_volume_lower hcomplete hRic ho hnormal hC hC1 hy
  have h8 : ENNReal.ofReal (2 : ℝ) ^ 3 = 8 := by norm_num
  rw [h8] at hvol
  have hnum : 8 * (M34.capBallVolumeCoefficient C * r ^ 3) ≤
      C⁻¹ * ((100 * C)⁻¹) ^ 3 := by
    have hbeta : 0 ≤ M34.capBallVolumeCoefficient C :=
      (M34.capBallVolumeCoefficient_pos hCpos).le
    calc
      _ ≤ 8 * (M34.capBallVolumeCoefficient C * (2 * C) ^ 3) := by
        gcongr
        exact hradius.2
      _ = _ := by
        unfold M34.capBallVolumeCoefficient
        field_simp [hCpos.ne']
  apply (ENNReal.mul_le_mul_iff_right (a := (8 : ℝ≥0∞))
    (by norm_num) (by norm_num)).mp
  have h8real : ENNReal.ofReal (8 : ℝ) = 8 := by norm_num
  rw [← h8real]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), h8real]
  exact (ENNReal.ofReal_le_ofReal hnum).trans (hreference.trans hvol)

end PoincareConjecture.CapCertificate
