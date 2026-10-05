import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.FreePhaseSeamWeak
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.BoundaryCompactness.Planar.CircleObservation

/-! The actual affine winding period preserves the retained circle
observation across the seam. A periodic boundary lift supplies that period.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareMT

open Proofs.M58

/-- Subtracting a retained winding period does not change the circle observation. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AngularPoint_sub_phase_period {k D : ℝ}
    (hperiod : angularPoint (k * D) = angularPoint 0) (u : ℝ) :
    angularPoint (k * (u - D)) = angularPoint (k * u) := by
  have hc : Real.cos (k * D) = 1 := by
    simpa only [angularPoint, Matrix.cons_val_zero, Real.cos_zero] using
      congrArg (fun p : LoopPlane => p 0) hperiod
  have hs : Real.sin (k * D) = 0 := by
    simpa only [angularPoint, Matrix.cons_val_one, Matrix.cons_val_zero, Real.sin_zero] using
      congrArg (fun p : LoopPlane => p 1) hperiod
  ext i
  fin_cases i <;> simp [angularPoint, mul_sub, Real.cos_sub, Real.sin_sub, hc, hs]

namespace M64

/-- A periodic target curve and its affine real lift give the required circle winding
period. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem circle_phase_period_of_periodic_lift {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (gamma : ℝ → C.Point)
    (hgamma : Function.Periodic gamma curvePeriod) (H : ℝ → ℝ) {D : ℝ}
    (hH : ∀ x, H (x + curvePeriod) = H x + D)
    (hquot : ∀ x, C.quotient (H x) = gamma x) :
    angularPoint ((curvePeriod / circumference) * D) = angularPoint 0 := by
  have hq : C.quotient (H 0 + D) = C.quotient (H 0) := by
    rw [← hH 0, hquot, hgamma 0, hquot]
  have hD : C.quotient D = C.quotient 0 := by
    change ((H 0 + D : ℝ) : AddCircle circumference) = (H 0 : AddCircle circumference) at hq
    rw [AddCircle.coe_add] at hq
    have hz : (D : AddCircle circumference) = 0 := add_left_cancel
      (hq.trans (add_zero (H 0 : AddCircle circumference)).symm)
    exact hz
  rw [← planarCircleObservation_quotient C D, hD, planarCircleObservation_quotient C 0,
    mul_zero]

end M64

namespace M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

/-- The affine real-phase extension retains the actual observed circle across the angular
seam. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem phase_seam_extension_observation
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hperiod : angularPoint (k * D) = angularPoint 0) :
    (fun p => R (e (m64AnnulusSeamExtend A.annulus.map p))) =ᵐ[
      volume.restrict m64AnnulusSeamDomain]
      fun p => angularPoint (k * m64AnnulusAffineSeamExtend A.phase D p) := by
  rw [Measure.restrict_congr_set m64AnnulusSeamDomain_ae_union]
  apply (ae_restrict_union_iff _ _ _).mpr
  constructor
  · filter_upwards [A.phase_observation, ae_restrict_mem isOpen_interior.measurableSet]
      with p hp hpS
    rw [m64AnnulusSeamExtend_right _ hpS, m64AnnulusAffineSeamExtend_right _ _ hpS]
    exact hp
  · have h := m64AnnulusSeam_translation_measurePreserving.quasiMeasurePreserving.ae
      A.phase_observation
    filter_upwards [h, ae_restrict_mem m64AnnulusSeamLeft_isOpen.measurableSet]
      with p hp hpL
    rw [m64AnnulusSeamExtend_left _ hpL, m64AnnulusAffineSeamExtend_left _ _ hpL,
      m64AngularPoint_sub_phase_period hperiod]
    exact hp

end M64FreeWeakPhaseAnnulus
end PoincareMT
