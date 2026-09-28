import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularAngles

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

noncomputable def m64AnnulusPolarMap (A : M64Annulus g c0 c1)
    (z : LoopPlane) : M :=
  A.map (annulusPoint (m60PlaneAngle z) (2 * ‖z‖ - 1))

theorem m64AnnulusPolarMap_eq_polar (A : M64Annulus g c0 c1)
    {z : LoopPlane} (hz : z ≠ 0) {theta : ℝ}
    (hpolar : ‖z‖ • Proofs.M58.angularPoint theta = z) :
    m64AnnulusPolarMap A z = A.map (annulusPoint theta (2 * ‖z‖ - 1)) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hangle : Proofs.M58.angularPoint (m60PlaneAngle z) =
      Proofs.M58.angularPoint theta := by
    have h := congrArg (fun w : LoopPlane => ‖z‖⁻¹ • w)
      ((m60PlaneAngle_polar z).trans hpolar.symm)
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using h
  exact m60Periodic_eq_of_angularPoint_eq
    (show Function.Periodic
      (fun x => A.map (annulusPoint x (2 * ‖z‖ - 1))) rampPeriod from
      fun x => A.periodic x (2 * ‖z‖ - 1)) hangle

theorem m64AnnulusPolarMap_polar (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) (theta : ℝ) :
    m64AnnulusPolarMap A (r • Proofs.M58.angularPoint theta) =
      A.map (annulusPoint theta (2 * r - 1)) := by
  have hn : ‖r • Proofs.M58.angularPoint theta‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      Proofs.M58.norm_angularPoint, mul_one]
  have hz : r • Proofs.M58.angularPoint theta ≠ 0 :=
    norm_pos_iff.mp (hn.symm ▸ hr)
  simpa only [hn] using
    m64AnnulusPolarMap_eq_polar A hz (theta := theta) (by rw [hn])

theorem m64AnnulusPolarMap_lower (A : M64Annulus g c0 c1) (theta : ℝ) :
    m64AnnulusPolarMap A ((1 / 2 : ℝ) • Proofs.M58.angularPoint theta) =
      c0 theta := by
  rw [m64AnnulusPolarMap_polar A (by norm_num),
    show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num, A.lower_boundary]

theorem m64AnnulusPolarMap_upper (A : M64Annulus g c0 c1) (theta : ℝ) :
    m64AnnulusPolarMap A (Proofs.M58.angularPoint theta) = c1 theta := by
  have h := m64AnnulusPolarMap_polar A (r := 1) (by norm_num) theta
  simpa only [one_smul, mul_one, show (2 : ℝ) - 1 = 1 by norm_num,
    A.upper_boundary] using h

theorem m64AnnulusPolarMap_radial_periodic (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) :
    Function.Periodic
      (fun theta => m64AnnulusPolarMap A (r • Proofs.M58.angularPoint theta))
      curvePeriod := by
  intro theta
  dsimp
  rw [m64AnnulusPolarMap_polar A hr (theta + curvePeriod),
    m64AnnulusPolarMap_polar A hr theta]
  exact A.periodic theta (2 * r - 1)

end PoincareConjecture
