import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.CoverJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Actual local invertibility of the periodic polar covering

The literal polar column determinant is nonzero away from radius zero.
The inverse function theorem therefore supplies the local neighborhood
identity needed for transporting openness to the covering strip.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

/-- The actual polar covering differential is invertible at every nonzero radius. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded
in `proof-work/tasks/M64/reports/annular-conjugate-open-surjective.md`. -/
theorem scalarCoverMap_fderiv_invertible {z : Cover} (hz : z.1 ≠ 0) :
    (fderiv ℝ scalarCoverMap z).IsInvertible := by
  let A := fderiv ℝ scalarCoverMap z
  let a : Plane := A (1, 0)
  let b : Plane := A (0, 1)
  have hdet : a 0 * b 1 - a 1 * b 0 ≠ 0 := by
    have h := scalarCoverMap_column_determinant z.1 z.2
    change a 0 * b 1 - a 1 * b 0 = 2 * Real.pi * z.1 at h
    rw [h]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hz
  have hinj : Function.Injective A := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change A v = 0 at hv
    have hsplit : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
    have h0 : a 0 * v.1 + b 0 * v.2 = 0 := by
      have h := congrArg (fun p : Plane => p 0) hv
      rw [hsplit, map_add, map_smul, map_smul] at h
      simpa only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, PiLp.zero_apply, mul_comm] using h
    have h1 : a 1 * v.1 + b 1 * v.2 = 0 := by
      have h := congrArg (fun p : Plane => p 1) hv
      rw [hsplit, map_add, map_smul, map_smul] at h
      simpa only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, PiLp.zero_apply, mul_comm] using h
    have hv0 : v.1 = 0 := by
      have hmul : (a 0 * b 1 - a 1 * b 0) * v.1 = 0 := by
        linear_combination b 1 * h0 - b 0 * h1
      exact (mul_eq_zero.mp hmul).resolve_left hdet
    have hv1 : v.2 = 0 := by
      have hmul : (a 0 * b 1 - a 1 * b 0) * v.2 = 0 := by
        linear_combination a 0 * h1 - a 1 * h0
      exact (mul_eq_zero.mp hmul).resolve_left hdet
    exact Prod.ext hv0 hv1
  have hdim : Module.finrank ℝ Cover = Module.finrank ℝ Plane := by simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨(LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    rfl⟩

/-- The literal periodic polar map sends the neighborhood filter onto the annular
neighborhood filter at every nonzero radius. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-conjugate-open-surjective.md`. -/
theorem scalarCoverMap_map_nhds {z : Cover} (hz : z.1 ≠ 0) :
    map scalarCoverMap (𝓝 z) = 𝓝 (scalarCoverMap z) := by
  obtain ⟨A, hA⟩ := scalarCoverMap_fderiv_invertible hz
  have hstrict := (scalarCoverMap_smooth.contDiffAt (x := z)).hasStrictFDerivAt (by simp)
  rw [← hA] at hstrict
  exact hstrict.map_nhds_eq_of_equiv

/-- The polar local inverse also transports punctured neighborhoods, so isolated fibers
remain isolated after lifting to the strip. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-conjugate-open-surjective.md`. -/
theorem scalarCoverMap_tendsto_nhdsNE {z : Cover} (hz : z.1 ≠ 0) :
    Tendsto scalarCoverMap (𝓝[≠] z) (𝓝[≠] scalarCoverMap z) := by
  obtain ⟨A, hA⟩ := scalarCoverMap_fderiv_invertible hz
  have hD : HasFDerivAt scalarCoverMap (A : Cover →L[ℝ] Plane) z := by
    rw [hA]
    exact (scalarCoverMap_smooth.differentiable (by simp) z).hasFDerivAt
  exact hD.tendsto_nhdsNE ⟨_, A.antilipschitz⟩

end PoincareMT.M64Uniformization
