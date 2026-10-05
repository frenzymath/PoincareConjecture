import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Circle.Lift
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Local.DiffeomorphLift

/-!
# The actual circle phase of an annular map

The quotient covering produces a real C1 phase on the parameter plane.
Uniqueness of lifts fixes its lower boundary and preserves the exact
period increment throughout the annulus. This is the topological input
for the circle-energy control of the conformal modulus.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

namespace PoincareMT

/-- The quotient covering constructs a genuine C1 real phase with exact lower trace and
winding increment. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64CircleAnnulus_exists_phase {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (f : LoopPlane → C.Point)
    (hf : ContMDiff (𝓡 2) (𝓡 1) 1 f)
    (hper : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (L0 : ℝ → ℝ) (hL0 : Continuous L0)
    (hzero : ∀ x, C.quotient (L0 x) = f (annulusPoint x 0))
    {degreeIncrement : ℝ} (hshift : ∀ x, L0 (x + curvePeriod) = L0 x + degreeIncrement) :
    ∃ L : LoopPlane → ℝ, ContDiff ℝ 1 L ∧
      (∀ p, C.quotient (L p) = f p) ∧
      (∀ x, L (annulusPoint x 0) = L0 x) ∧
      ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + degreeIncrement := by
  let := C.chartedSpace
  let cov := AddCircle.isCoveringMap_coe circumference
  obtain ⟨L, hL, -⟩ := cov.existsUnique_continuousMap_lifts
    ⟨f, hf.continuous⟩ (annulusPoint 0 0) (L0 0) (hzero 0)
  have hquot (p : LoopPlane) : C.quotient (L p) = f p := congrFun hL.2 p
  have hlower : ∀ x, L (annulusPoint x 0) = L0 x := by
    have hc : Continuous (fun x => annulusPoint x 0) := by unfold annulusPoint; fun_prop
    have heq := cov.eq_of_comp_eq (L.continuous.comp hc) hL0
      (show (fun x => (L (annulusPoint x 0) : AddCircle circumference)) =
        (fun x => (L0 x : AddCircle circumference)) from by
          funext x
          exact (hquot _).trans (hzero x).symm) 0 hL.1
    exact congrFun heq
  have hdegree : (degreeIncrement : AddCircle circumference) = 0 := by
    have hh := hper 0 0
    rw [← hzero, ← hzero, hshift] at hh
    change ((L0 0 + degreeIncrement : ℝ) : AddCircle circumference) =
      (L0 0 : AddCircle circumference) at hh
    rw [AddCircle.coe_add] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  have hregular : ContDiff ℝ 1 L := by
    apply contMDiff_iff_contDiff.mp
    intro p
    apply (C.quotient_local_diffeomorph (L p)).contMDiffAt_of_comp
      (I := 𝓡 2) (m := 1) (by decide) L.continuous.continuousAt
    change ContMDiffAt (𝓡 2) (𝓡 1) 1 (C.quotient ∘ L) p
    rw [show C.quotient ∘ L = f from funext hquot]
    exact hf p
  refine ⟨L, hregular, hquot, hlower, ?_⟩
  have htranslate : Continuous (fun p : LoopPlane =>
      annulusPoint (p 0 + curvePeriod) (p 1)) := by unfold annulusPoint; fun_prop
  have hbase : Continuous (fun p : LoopPlane => annulusPoint (p 0) (p 1)) := by
    unfold annulusPoint
    fun_prop
  have heq := cov.eq_of_comp_eq (L.continuous.comp htranslate)
    ((L.continuous.comp hbase).add continuous_const)
    (show (fun p : LoopPlane => (L (annulusPoint (p 0 + curvePeriod) (p 1)) :
        AddCircle circumference)) =
      (fun p : LoopPlane => ((L (annulusPoint (p 0) (p 1)) + degreeIncrement : ℝ) :
        AddCircle circumference)) from by
          funext p
          rw [AddCircle.coe_add, hdegree, add_zero]
          exact (hquot _).trans ((hper _ _).trans (hquot _).symm))
    (annulusPoint 0 0) (by
      change L (annulusPoint (0 + curvePeriod) 0) = L (annulusPoint 0 0) + degreeIncrement
      rw [hlower, hlower]
      exact hshift 0)
  intro x s
  simpa [Function.comp_def, annulusPoint] using congrFun heq (annulusPoint x s)

end PoincareMT
