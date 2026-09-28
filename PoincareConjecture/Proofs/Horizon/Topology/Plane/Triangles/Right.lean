


import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Between









set_option autoImplicit false

open Set
open scoped Matrix Convex

namespace Poincare.Topology.Plane.Triangles

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

private theorem right_triangle_independent {ε : ℝ} (hε : 0 < ε) :
    AffineIndependent ℝ (![!₂[0, 0], !₂[ε, 0], !₂[0, ε]] : Fin 3 → E2) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hsum i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hsum
  have hx : w 1 * ε = 0 := by
    simpa [Fin.sum_univ_succ] using congrArg (fun z : E2 => z 0) hsum
  have hy : w 2 * ε = 0 := by
    simpa [Fin.sum_univ_succ] using congrArg (fun z : E2 => z 1) hsum
  have hw1 : w 1 = 0 := (mul_eq_zero.mp hx).resolve_right hε.ne'
  have hw2 : w 2 = 0 := (mul_eq_zero.mp hy).resolve_right hε.ne'
  have hw0 : w 0 = 0 := by simpa [Fin.sum_univ_succ, hw1, hw2] using hw
  fin_cases i <;> assumption


noncomputable def rightTriangleBasis {ε : ℝ} (hε : 0 < ε) : AffineBasis (Fin 3) ℝ E2 :=
  ⟨![!₂[0, 0], !₂[ε, 0], !₂[0, ε]], right_triangle_independent hε,
    (right_triangle_independent hε).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp [E2, finrank_euclideanSpace])⟩

@[simp] theorem rightTriangleBasis_apply {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    rightTriangleBasis hε i = ![!₂[0, 0], !₂[ε, 0], !₂[0, ε]] i := rfl


theorem rightTriangleBasis_coord {ε : ℝ} (hε : 0 < ε) (z : E2) (i : Fin 3) :
    (rightTriangleBasis hε).coord i z = ![1 - z 0 / ε - z 1 / ε, z 0 / ε, z 1 / ε] i := by
  let w : Fin 3 → ℝ := ![1 - z 0 / ε - z 1 / ε, z 0 / ε, z 1 / ε]
  have hw : ∑ j, w j = 1 := by simp [w, Fin.sum_univ_succ]
  have hz : ∑ j, w j • rightTriangleBasis hε j = z := by
    ext k
    fin_cases k <;> simp [w, Fin.sum_univ_succ, hε.ne']
  rw [← Finset.affineCombination_eq_linear_combination _ _ _ hw] at hz
  calc
    (rightTriangleBasis hε).coord i z =
        (rightTriangleBasis hε).coord i
          (Finset.univ.affineCombination ℝ (rightTriangleBasis hε) w) :=
      congrArg ((rightTriangleBasis hε).coord i) hz.symm
    _ = w i :=
      (rightTriangleBasis hε).coord_apply_combination_of_mem (Finset.mem_univ i) hw


theorem mem_rightTriangleBasis_convexHull {ε : ℝ} (hε : 0 < ε) (z : E2) :
    z ∈ convexHull ℝ (range (rightTriangleBasis hε)) ↔
      0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 0 + z 1 ≤ ε := by
  rw [AffineBasis.convexHull_eq_nonneg_coord]
  simp only [mem_ofPred_eq, rightTriangleBasis_coord, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
  rw [show 1 - z 0 / ε - z 1 / ε = 1 - (z 0 + z 1) / ε by ring,
    sub_nonneg, div_le_one hε, le_div_iff₀ hε, le_div_iff₀ hε, zero_mul]
  tauto

theorem rightTriangleBasis_convexHull {ε : ℝ} (hε : 0 < ε) :
    convexHull ℝ (range (rightTriangleBasis hε)) =
      {z : E2 | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 0 + z 1 ≤ ε} :=
  Set.ext (mem_rightTriangleBasis_convexHull hε)

end Poincare.Topology.Plane.Triangles
