import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Polar.CircleColumn

/-! The angular column is bounded by the two actual planar derivative columns.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT

open Proofs.M58

/-- The actual squared angular column is bounded by twice the squared radius times the two
Cartesian column squares. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64MorreyPolarAngularColumn_norm_sq_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : LoopPlane) (rho : ℝ) (V : Fin 2 → LoopPlane → E) (p : LoopPlane) :
    ‖m64MorreyPolarAngularColumn a rho V p‖ ^ 2 ≤
      2 * (rho * Real.exp (-p 1)) ^ 2 *
        (‖V 0 (m64MorreyPolarStrip a rho p)‖ ^ 2 +
          ‖V 1 (m64MorreyPolarStrip a rho p)‖ ^ 2) := by
  let r := rho * Real.exp (-p 1)
  let t := p 0 - Real.pi
  let W := fun i => V i (m64MorreyPolarStrip a rho p)
  let U := fun i => (r * angularVector t i) • W i
  have hunit : ‖angularVector t‖ = 1 := by
    simp [angularVector, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
  have hcomp (i : Fin 2) : |angularVector t i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hunit] using PiLp.norm_apply_le (angularVector t) i
  have hnorm (i : Fin 2) : ‖U i‖ ≤ |r| * ‖W i‖ := by
    dsimp only [U]
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg r) (hcomp i)) (norm_nonneg _)
  have hs (i : Fin 2) : ‖U i‖ ^ 2 ≤ r ^ 2 * ‖W i‖ ^ 2 := by
    simpa only [mul_pow, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg r) (norm_nonneg _))).mpr (hnorm i)
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  have hZ := m64MorreyPolarAngularColumn_circle a rho V (p 0) (p 1)
  rw [hpoint] at hZ
  change m64MorreyPolarAngularColumn a rho V p = U 0 + U 1 at hZ
  rw [hZ]
  have hsum := (sq_le_sq₀ (norm_nonneg (U 0 + U 1))
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le (U 0) (U 1))
  change ‖U 0 + U 1‖ ^ 2 ≤ 2 * r ^ 2 * (‖W 0‖ ^ 2 + ‖W 1‖ ^ 2)
  nlinarith [hs 0, hs 1, sq_nonneg (‖U 0‖ - ‖U 1‖)]

end PoincareMT
