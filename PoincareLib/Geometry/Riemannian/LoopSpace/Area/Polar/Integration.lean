import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Angular
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Polar integration on the contract's Euclidean disk

The area estimate for Morgan--Tian Corollary 18.28, printed p. 434, uses
ordinary Euclidean volume on LoopPlane. We transport Mathlib's polar
change-of-variables formula through volume-preserving coordinate maps.
See the task's polar-area derivation.
-/

set_option autoImplicit false

open Set MeasureTheory Real
open scoped Manifold ContDiff Topology

namespace PoincareMT.LoopSpace

/-- The measurable coordinate equivalence from the contract plane to a
real product. Source: MT Definition 18.17, p. 430, polar-area derivation. -/
noncomputable def loopPlaneEquivProd : LoopPlane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

/-- This coordinate equivalence preserves the specified Euclidean volume.
Source: MT Definition 18.17, p. 430, polar-area derivation. -/
theorem measurePreserving_loopPlaneEquivProd : MeasurePreserving loopPlaneEquivProd :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

/-- Mathlib's polar map has the contract's standard angular coordinates.
Source: MT Corollary 18.28, p. 434, polar-area derivation. -/
theorem loopPlaneEquivProd_symm_polar (p : ℝ × ℝ) :
    loopPlaneEquivProd.symm (polarCoord.symm p) = p.1 • angularPoint p.2 := by
  ext i
  fin_cases i <;> rfl

/-- Polar integration on LoopPlane with the exact radial Jacobian.
Source: MT Corollary 18.28, p. 434, polar-area derivation. -/
theorem integral_polar_loopPlane (f : LoopPlane → ℝ) :
    (∫ p in polarCoord.target, p.1 * f (p.1 • angularPoint p.2)) = ∫ z, f z := by
  calc
    _ = ∫ p in polarCoord.target, p.1 • f (loopPlaneEquivProd.symm (polarCoord.symm p)) := by
      simp only [loopPlaneEquivProd_symm_polar, smul_eq_mul]
    _ = ∫ p : ℝ × ℝ, f (loopPlaneEquivProd.symm p) :=
      integral_comp_polarCoord_symm (fun p => f (loopPlaneEquivProd.symm p))
    _ = ∫ z, f z := measurePreserving_loopPlaneEquivProd.symm.integral_comp' f

/-- Polar integration restricted to the closed unit disk. Its boundary
and the omitted polar ray cause no extra terms. Source: MT Corollary 18.28, p. 434. -/
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

end PoincareMT.LoopSpace
