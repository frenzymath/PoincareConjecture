import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarStrongApproximation







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Proofs.M58



theorem m64AngularVector_periodic : Function.Periodic angularVector curvePeriod := by
  intro x
  ext i
  fin_cases i <;> simp [angularVector, curvePeriod, Real.sin_add_two_pi, Real.cos_add_two_pi]



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

end PoincareConjecture
