import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.BoundaryCompactness.Boundary.PolarEnergy
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Circle.PhaseEnergy

/-! The actual boundary oscillation estimate on an upper semicircle.
Derivatives are needed only on the open arc; continuity supplies its two
boundary endpoints. The integrability hypotheses are the Fubini slice
conditions furnished by the actual shell energy estimate.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT.M64

open Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The right semicircle endpoint is its literal radial-boundary point. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem boundaryPolarStrip_right_endpoint (x rho s : ℝ) :
    boundaryPolarStrip x rho (annulusPoint 0 s) =
      annulusPoint (x + rho * Real.exp (-s)) 0 := by
  ext i
  fin_cases i <;> simp [boundaryPolarStrip, annulusPoint, angularPoint]

/-- The left semicircle endpoint is its literal radial-boundary point. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem boundaryPolarStrip_left_endpoint (x rho s : ℝ) :
    boundaryPolarStrip x rho (annulusPoint curvePeriod s) =
      annulusPoint (x - rho * Real.exp (-s)) 0 := by
  have hangle : curvePeriod / 2 = Real.pi := by unfold curvePeriod; ring
  ext i
  fin_cases i <;> simp [boundaryPolarStrip, annulusPoint, angularPoint, hangle, sub_eq_add_neg]

/-- Interior arc differentiation and continuous endpoints give the actual semicircle
oscillation estimate. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
theorem boundary_semicircle_oscillation
    (L : LoopPlane → ℝ) (hLc : Continuous L) (hL : ContDiffOn ℝ 1 L S)
    {x rho : ℝ} (hrho : 0 < rho) (hx : rho < x)
    (hP : x + rho < curvePeriod) (hr : rho < 1)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hD : IntervalIntegrable (fun theta =>
      boundaryAngularDerivative L x rho (annulusPoint theta s)) volume 0 curvePeriod)
    (hD2 : IntervalIntegrable (fun theta =>
      boundaryAngularDerivative L x rho (annulusPoint theta s) ^ 2) volume 0 curvePeriod) :
    (L (annulusPoint (x + rho * Real.exp (-s)) 0) -
      L (annulusPoint (x - rho * Real.exp (-s)) 0)) ^ 2 ≤
        curvePeriod * ∫ theta in Icc (0 : ℝ) curvePeriod,
          boundaryAngularDerivative L x rho (annulusPoint theta s) ^ 2 := by
  let w := fun theta => L (boundaryPolarStrip x rho (annulusPoint theta s))
  have hw : Continuous w := by
    apply hLc.comp
    apply (boundaryPolarStrip_contDiff x rho).continuous.comp
    unfold annulusPoint
    fun_prop
  have hd (theta : ℝ) (htheta : theta ∈ Ioo (0 : ℝ) curvePeriod) :
      HasDerivAt w (boundaryAngularDerivative L x rho (annulusPoint theta s)) theta := by
    have hp : annulusPoint theta s ∈ S :=
      (m64AnnulusInterior_coordinates _).mpr ⟨htheta.1, htheta.2, hs.1, hs.2⟩
    have himage := upperBoundaryShell_subset_interior hx hP hr
      (boundaryPolarStrip_mapsTo_shell x hrho hp)
    have hLd := ((hL _ himage).contDiffAt (isOpen_interior.mem_nhds himage)).differentiableAt
      one_ne_zero
    have hPd := (boundaryPolarStrip_contDiff x rho).differentiable (by simp)
      (annulusPoint theta s)
    have hcomp := (hLd.hasFDerivAt.comp (annulusPoint theta s) hPd.hasFDerivAt).comp_hasDerivAt
      theta (m64AnnulusPoint_horizontal_hasDerivAt s theta)
    have hdir : fderiv ℝ (boundaryPolarStrip x rho) (annulusPoint theta s) e0 =
        (rho * Real.exp (-s) / 2) • angularVector (theta / 2) := by
      rw [boundaryPolarStrip_fderiv]
      simp [annulusPoint]
      module
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply] at hcomp
    rw [hdir] at hcomp
    simpa only [boundaryAngularDerivative, w, annulusPoint,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hcomp
  have hP0 : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hP0
    hw.continuousOn hd hD
  have hsq := SpectralHeatNative.integral_sq_le_time_mul_integral_sq hP0 hD hD2
  rw [hFTC] at hsq
  have hw0 : w 0 = L (annulusPoint (x + rho * Real.exp (-s)) 0) := by
    exact congrArg L (boundaryPolarStrip_right_endpoint x rho s)
  have hwP : w curvePeriod = L (annulusPoint (x - rho * Real.exp (-s)) 0) := by
    exact congrArg L (boundaryPolarStrip_left_endpoint x rho s)
  rw [hw0, hwP, intervalIntegral.integral_of_le hP0, ← integral_Icc_eq_integral_Ioc] at hsq
  nlinarith [hsq]

end PoincareMT.M64
