import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityPullback
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformalPullback

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture.M65Boundary

private def diskRotation (p : ℂ) (z : LoopPlane) : LoopPlane :=
  orthonormalBasisOneI.repr (p * orthonormalBasisOneI.repr.symm z)

private theorem contDiff_diskRotation (p : ℂ) : ContDiff ℝ ∞ (diskRotation p) :=
  orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.comp
    ((contDiff_const.mul contDiff_id).comp
      orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff)

private theorem norm_diskRotation (p : ℂ) (z : LoopPlane) :
    ‖diskRotation p z‖ = ‖p‖ * ‖z‖ := by
  rw [diskRotation, orthonormalBasisOneI.repr.norm_map, norm_mul,
    orthonormalBasisOneI.repr.symm.norm_map]

private theorem diskRotation_inverse {p : ℂ} (hp : p ≠ 0) (z : LoopPlane) :
    diskRotation p⁻¹ (diskRotation p z) = z := by
  simp only [diskRotation, LinearIsometryEquiv.symm_apply_apply, ← mul_assoc,
    inv_mul_cancel₀ hp, one_mul, LinearIsometryEquiv.apply_symm_apply]

private theorem diskRotation_boundary_bound {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      m65CircleBoundaryMeasure.map (diskRotation p) ≤ C • m65CircleBoundaryMeasure := by
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  have hinv : ‖p⁻¹‖ = 1 := by rw [norm_inv, hp, inv_one]
  apply m65SmoothCircle_map_bound (diskRotation p) (diskRotation p⁻¹)
    (contDiff_diskRotation p).continuous
    (fun _ _ => ((contDiff_diskRotation p⁻¹).of_le (by simp)).contDiffAt)
  · intro z hz
    rw [norm_diskRotation, hp, hz, one_mul]
  · intro z hz
    rw [norm_diskRotation, hinv, hz, one_mul]
  · intro z _
    exact diskRotation_inverse hp0 z
  · intro z _
    simpa only [inv_inv] using diskRotation_inverse (inv_ne_zero hp0) z

theorem boundaryCoordinate_diameter (p : ℂ) (t : ℝ) :
    diskBoundaryCoordinate p (t • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      orthonormalBasisOneI.repr (p * orthonormalBasisOneI.repr.symm
        (Proofs.M58.angularPoint t)) := by
  have he : orthonormalBasisOneI.repr.symm
      (t • EuclideanSpace.basisFun (Fin 2) ℝ 0) = (t : ℂ) := by
    simp [EuclideanSpace.basisFun_apply]
  rw [diskBoundaryCoordinate, he, M65StrictTrace.boundaryCoordinate,
    mul_comm I (t : ℂ), exp_ofReal_mul_I]
  congr 2

theorem diameter_measure_bound {p : ℂ} (hp : ‖p‖ = 1) {R : ℝ} (hR : R ≤ Real.pi) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (volume.restrict (Icc (-R) R)).map
        (fun t => diskBoundaryCoordinate p (t • EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤
          C • m65CircleBoundaryMeasure := by
  obtain ⟨C, hC, hrot⟩ := diskRotation_boundary_bound hp
  have hsub : Icc (-R) R ⊆ Icc (-Real.pi) Real.pi :=
    Icc_subset_Icc (neg_le_neg hR) hR
  have hdom : (volume.restrict (Icc (-R) R)).map Proofs.M58.angularPoint ≤
      m65CircleBoundaryMeasure :=
    Measure.map_mono (Measure.restrict_mono hsub le_rfl)
      Proofs.M58.contDiff_angularPoint.continuous.measurable
  have heq : (fun t => diskBoundaryCoordinate p (t • EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
      diskRotation p ∘ Proofs.M58.angularPoint := funext (boundaryCoordinate_diameter p)
  refine ⟨C, hC, ?_⟩
  rw [heq, ← Measure.map_map (contDiff_diskRotation p).continuous.measurable
    Proofs.M58.contDiff_angularPoint.continuous.measurable]
  exact (Measure.map_mono hdom (contDiff_diskRotation p).continuous.measurable).trans hrot

theorem diameter_boundary_graph {p : ℂ} (hp : ‖p‖ = 1) {R : ℝ} (hR : R ≤ Real.pi)
    (f : ℕ → LoopPlane → ℝ)
    (C : ℕ → Lp ℝ 2 m65CircleBoundaryMeasure) (b : Lp ℝ 2 m65CircleBoundaryMeasure)
    (hC : ∀ n, C n =ᵐ[m65CircleBoundaryMeasure] f n)
    (hlim : Tendsto C atTop (𝓝 b)) :
    ∃ (B : ℕ → Lp ℝ 2 (volume.restrict (Icc (-R) R)))
      (B0 : Lp ℝ 2 (volume.restrict (Icc (-R) R))),
      (∀ n, B n =ᵐ[volume.restrict (Icc (-R) R)] fun t =>
        f n (diskBoundaryCoordinate p (t • EuclideanSpace.basisFun (Fin 2) ℝ 0))) ∧
      B0 =ᵐ[volume.restrict (Icc (-R) R)] (fun t =>
        b (diskBoundaryCoordinate p (t • EuclideanSpace.basisFun (Fin 2) ℝ 0))) ∧
      Tendsto B atTop (𝓝 B0) := by
  let P := fun t : ℝ => diskBoundaryCoordinate p (t • EuclideanSpace.basisFun (Fin 2) ℝ 0)
  have hP : Continuous P := (contDiff_diskBoundaryCoordinate p).continuous.comp
    (continuous_id.smul continuous_const)
  obtain ⟨K, hK, hdom⟩ := diameter_measure_bound hp hR
  let T : Lp ℝ 2 m65CircleBoundaryMeasure →L[ℝ]
      Lp ℝ 2 (volume.restrict (Icc (-R) R)) :=
    ChartLpNative.dominatedPullbackL2 P hP.measurable.aemeasurable hK hdom
  have hT (v : Lp ℝ 2 m65CircleBoundaryMeasure) :
      T v =ᵐ[volume.restrict (Icc (-R) R)] fun t => v (P t) :=
    ChartLpNative.dominatedPullbackL2_coe _ _ _ _ v
  refine ⟨fun n => T (C n), T b, ?_, hT b, (T.continuous.tendsto b).comp hlim⟩
  intro n
  exact (hT (C n)).trans (ae_of_ae_map hP.measurable.aemeasurable
    (ae_mono hdom (Measure.ae_smul_measure (hC n) K)))

end PoincareConjecture.M65Boundary
