import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.EnergyIntegral
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabelingConnection










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in


theorem m65Mfderiv_diskDilation (f : LoopPlane → M) (r : ℝ) (z v : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (r • z)) :
    mfderiv (𝓡 2) (𝓡 n) (fun w => f (r • w)) z v =
      r • mfderiv (𝓡 2) (𝓡 n) f (r • z) v := by
  have hscale : HasFDerivAt (fun w : LoopPlane => r • w)
      (r • ContinuousLinearMap.id ℝ LoopPlane) z :=
    (hasFDerivAt_id z).const_smul r
  have h := mfderiv_comp_apply (f := fun w : LoopPlane => r • w) (g := f) z hf
    hscale.differentiableAt.mdifferentiableAt v
  rw [mfderiv_eq_fderiv, hscale.fderiv] at h
  simpa +instances only [Function.comp_def, smul_apply,
    ContinuousLinearMap.id_apply, map_smul] using! h



theorem m65AreaGram_diskDilation (g : RiemannianMetric n M)
    (f : LoopPlane → M) (r : ℝ) (z : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (r • z)) :
    m60AreaGram g (fun w => f (r • w)) z = r ^ 2 • m60AreaGram g f (r • z) := by
  ext i j
  dsimp only [m60AreaGram]
  rw [m65Mfderiv_diskDilation f r z _ hf, m65Mfderiv_diskDilation f r z _ hf]
  simp only [map_smul, smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring



theorem m65EnergyDensity_diskDilation (g : RiemannianMetric n M)
    (f : LoopPlane → M) (r : ℝ) (z : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (r • z)) :
    m60EnergyDensity g (fun w => f (r • w)) z = r ^ 2 * m60EnergyDensity g f (r • z) := by
  rw [m60EnergyDensity, m65AreaGram_diskDilation g f r z hf, Matrix.trace_smul]
  change (1 / 2 : ℝ) * (r ^ 2 * Matrix.trace (m60AreaGram g f (r • z))) = _
  dsimp only [m60EnergyDensity]
  ring




theorem m65DiskDilation_mem_interior {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {z : LoopPlane} (hz : z ∈ loopDiskSet) : r • z ∈ Metric.ball (0 : LoopPlane) 1 := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  exact (mul_le_mul_of_nonneg_left hz' hr).trans_lt (by simpa using hr1)

end PoincareConjecture
