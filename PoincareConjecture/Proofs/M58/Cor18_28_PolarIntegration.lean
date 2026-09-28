import PoincareConjecture.Proofs.M58.Sec18_4_LoopLength
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace










set_option autoImplicit false

open Set MeasureTheory Real
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M58



noncomputable def loopPlaneEquivProd : LoopPlane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow



theorem measurePreserving_loopPlaneEquivProd : MeasurePreserving loopPlaneEquivProd :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))



theorem loopPlaneEquivProd_symm_polar (p : ℝ × ℝ) :
    loopPlaneEquivProd.symm (polarCoord.symm p) = p.1 • angularPoint p.2 := by
  ext i
  fin_cases i <;> rfl



theorem integral_polar_loopPlane (f : LoopPlane → ℝ) :
    (∫ p in polarCoord.target, p.1 * f (p.1 • angularPoint p.2)) = ∫ z, f z := by
  calc
    _ = ∫ p in polarCoord.target, p.1 • f (loopPlaneEquivProd.symm (polarCoord.symm p)) := by
      simp only [loopPlaneEquivProd_symm_polar, smul_eq_mul]
    _ = ∫ p : ℝ × ℝ, f (loopPlaneEquivProd.symm p) :=
      integral_comp_polarCoord_symm (fun p => f (loopPlaneEquivProd.symm p))
    _ = ∫ z, f z := measurePreserving_loopPlaneEquivProd.symm.integral_comp' f



theorem integral_loopDisk_polar (f : LoopPlane → ℝ) :
    (∫ z in loopDiskSet, f z) =
      ∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioo (-π) π, p.1 * f (p.1 • angularPoint p.2) := by
  classical
  let S : Set (ℝ × ℝ) := Iic (1 : ℝ) ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Iic.prod MeasurableSet.univ
  have hset : S ∩ polarCoord.target = Ioc (0 : ℝ) 1 ×ˢ Ioo (-π) π := by
    ext p
    simp only [S, polarCoord_target, mem_inter_iff, mem_prod, mem_Iic, mem_univ,
      and_true, mem_Ioi, mem_Ioc, mem_Ioo]
    tauto
  rw [← integral_indicator (s := loopDiskSet) Metric.isClosed_closedBall.measurableSet,
    ← integral_polar_loopPlane]
  calc
    _ = ∫ p in polarCoord.target,
        S.indicator (fun p => p.1 * f (p.1 • angularPoint p.2)) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hr : 0 < p.1 := hp.1
      have hnorm : ‖p.1 • angularPoint p.2‖ = p.1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_angularPoint, mul_one]
      have hmem : p.1 • angularPoint p.2 ∈ loopDiskSet ↔ p ∈ S := by
        simp only [loopDiskSet, mem_closedBall_zero_iff, hnorm, S, mem_prod,
          mem_Iic, mem_univ, and_true]
      dsimp only
      by_cases h : p ∈ S
      · erw [indicator_of_mem (hmem.mpr h), indicator_of_mem h]
      · erw [indicator_of_notMem (mt hmem.mp h), indicator_of_notMem h, mul_zero]
    _ = _ := by rw [integral_indicator hS, Measure.restrict_restrict hS, hset]

end PoincareConjecture.Proofs.M58
