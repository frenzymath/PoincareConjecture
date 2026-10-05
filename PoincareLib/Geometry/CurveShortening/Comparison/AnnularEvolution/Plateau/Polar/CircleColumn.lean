import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Polar.StrongApproximation

/-! The actual angular weak column is literally periodic in the circle parameter.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT

open Proofs.M58

/-- The actual unit angular tangent vector is periodic. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449. -/
theorem m64AngularVector_periodic : Function.Periodic angularVector curvePeriod := by
  intro x
  ext i
  fin_cases i <;> simp [angularVector, curvePeriod, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- The actual angular weak column has the literal two-coordinate polar formula. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64MorreyPolarAngularColumn_circle
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a : LoopPlane) (rho : ℝ) (V : Fin 2 → LoopPlane → E) (x s : ℝ) :
    m64MorreyPolarAngularColumn a rho V (annulusPoint x s) =
      (rho * Real.exp (-s) * angularVector (x - Real.pi) 0) •
        V 0 (m64MorreyPolarStrip a rho (annulusPoint x s)) +
      (rho * Real.exp (-s) * angularVector (x - Real.pi) 1) •
        V 1 (m64MorreyPolarStrip a rho (annulusPoint x s)) := by
  unfold m64MorreyPolarAngularColumn
  rw [m64MorreyPolarStrip_fderiv]
  simp [annulusPoint]

/-- The actual angular weak column is periodic even for arbitrary original column
representatives. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64MorreyPolarAngularColumn_periodic
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a : LoopPlane) (rho : ℝ) (V : Fin 2 → LoopPlane → E) (s : ℝ) :
    Function.Periodic (fun x => m64MorreyPolarAngularColumn a rho V (annulusPoint x s))
      curvePeriod := by
  intro x
  dsimp only
  rw [m64MorreyPolarAngularColumn_circle, m64MorreyPolarAngularColumn_circle,
    m64MorreyPolarStrip_periodic]
  have hx : x + curvePeriod - Real.pi = (x - Real.pi) + curvePeriod := by ring
  rw [hx, m64AngularVector_periodic]

end PoincareMT
