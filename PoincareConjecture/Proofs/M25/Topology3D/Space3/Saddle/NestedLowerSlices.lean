import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightCoordinates

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem slice_radial_tests :
    let H : ℝ := 17 / 16
    let U : ℝ → ℝ → ℝ := fun t r =>
      r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
    ∀ v : E2,
      v 0 / ‖v‖ ∈ Set.Icc (-1 : ℝ) 1 ∧
      ∀ d : ℝ,
        (heightCoordinates.symm (v, H + d) ∈
            (nestedReferenceBallChart d).closedRegion ↔
          ‖v‖ ≤ 1 ∧ H ≤ U (v 0 / ‖v‖) ‖v‖) ∧
        (heightCoordinates.symm (v, H + d) ∈
            (nestedReferenceBallChart d).inside ↔
          ‖v‖ ≤ 1 ∧ H < U (v 0 / ‖v‖) ‖v‖) ∧
        (heightCoordinates.symm (v, H + d) ∈
            (nestedReferenceBallChart d).boundary ↔
          ‖v‖ ≤ 1 ∧ U (v 0 / ‖v‖) ‖v‖ = H) := by
  let H : ℝ := 17 / 16
  let U : ℝ → ℝ → ℝ := fun t r =>
    r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
  change ∀ v : E2, v 0 / ‖v‖ ∈ Icc (-1 : ℝ) 1 ∧ _
  intro v
  let r := ‖v‖
  let t := v 0 / r
  have hr0 : 0 ≤ r := norm_nonneg _
  have hnorm : r ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [r, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hcoord : -r ≤ v 0 ∧ v 0 ≤ r := by
    constructor <;> nlinarith only [hnorm, hr0, sq_nonneg (v 1)]
  have ht : t ∈ Icc (-1 : ℝ) 1 := by
    by_cases hz : r = 0
    · simp only [t, hz, div_zero]
      norm_num
    · have hr : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
      constructor
      · exact (le_div_iff₀ hr).mpr (by simpa only [neg_mul, one_mul] using hcoord.1)
      · exact (div_le_iff₀ hr).mpr (by simpa only [one_mul] using hcoord.2)
  have hangle : r * t = v 0 := by
    by_cases hz : r = 0
    · have hv : v = 0 := norm_eq_zero.mp hz
      have hv0 : v 0 = 0 := congrArg (fun x : E2 => x 0) hv
      rw [hz, zero_mul, hv0]
    · dsimp only [t]
      field_simp [hz]
  let A : ℝ := r ^ 2 + (H - r ^ 2 - v 0 / 32) ^ 2
  have halgebra :
      (A ≤ 1 ↔ r ≤ 1 ∧ H ≤ U t r) ∧
      (A < 1 ↔ r ≤ 1 ∧ H < U t r) ∧
      (A = 1 ↔ r ≤ 1 ∧ U t r = H) := by
    by_cases hr : r ≤ 1
    · let a := Real.sqrt (1 - r ^ 2)
      let L := r ^ 2 - a + v 0 / 32
      have ha0 : 0 ≤ a := Real.sqrt_nonneg _
      have hrsq : r ^ 2 ≤ 1 := by nlinarith only [hr0, hr]
      have ha2 : a ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hrsq)
      have hL : L ≤ 33 / 32 := by
        dsimp only [L]
        linarith only [hrsq, ha0, hcoord.2, hr]
      have hpos : 0 < H - L := by dsimp only [H]; linarith only [hL]
      have hU : U t r = r ^ 2 + a + v 0 / 32 := by
        dsimp only [U]
        rw [hangle]
      have hfactor : A - 1 = (H - U t r) * (H - L) := by
        calc
          A - 1 = (H - r ^ 2 - v 0 / 32) ^ 2 - a ^ 2 := by
            dsimp only [A]
            linarith only [ha2]
          _ = (H - U t r) * (H - L) := by rw [hU]; dsimp only [L]; ring
      have hle : A ≤ 1 ↔ H ≤ U t r := by
        calc
          (A ≤ 1) ↔ A - 1 ≤ 0 := sub_nonpos.symm
          _ ↔ (H - U t r) * (H - L) ≤ 0 * (H - L) := by rw [hfactor, zero_mul]
          _ ↔ H - U t r ≤ 0 := mul_le_mul_iff_left₀ hpos
          _ ↔ H ≤ U t r := sub_nonpos
      have hlt : A < 1 ↔ H < U t r := by
        calc
          (A < 1) ↔ A - 1 < 0 := sub_neg.symm
          _ ↔ (H - U t r) * (H - L) < 0 * (H - L) := by rw [hfactor, zero_mul]
          _ ↔ H - U t r < 0 := mul_lt_mul_iff_left₀ hpos
          _ ↔ H < U t r := sub_neg
      have heq : A = 1 ↔ U t r = H := by
        calc
          (A = 1) ↔ A - 1 = 0 := sub_eq_zero.symm
          _ ↔ (H - U t r) * (H - L) = 0 := by rw [hfactor]
          _ ↔ H - U t r = 0 := by simp only [mul_eq_zero, hpos.ne', or_false]
          _ ↔ U t r = H := sub_eq_zero.trans eq_comm
      simpa only [hr, true_and] using And.intro hle (And.intro hlt heq)
    · have hgt : 1 < A := by
        dsimp only [A]
        nlinarith only [lt_of_not_ge hr, sq_nonneg (H - r ^ 2 - v 0 / 32)]
      simp only [hr, false_and, not_le_of_gt hgt, hgt.not_gt, hgt.ne', iff_self, and_self]
  refine ⟨ht, ?_⟩
  intro d
  let y := heightCoordinates.symm (v, H + d)
  have hy0 : y 0 = v 0 := by dsimp only [y]; rw [heightCoordinates_symm_apply]; rfl
  have hy1 : y 1 = v 1 := by dsimp only [y]; rw [heightCoordinates_symm_apply]; rfl
  have hy2 : y 2 = H + d := by dsimp only [y]; rw [heightCoordinates_symm_apply]; rfl
  have hsum : (y 0) ^ 2 + (y 1) ^ 2 = r ^ 2 := by rw [hy0, hy1, hnorm]
  have hres : y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d =
      H - r ^ 2 - v 0 / 32 := by
    rw [hy0, hy1, hy2, hnorm]
    ring
  have hregions : (y ∈ (nestedReferenceBallChart d).inside ↔ A < 1) ∧
      (y ∈ (nestedReferenceBallChart d).closedRegion ↔ A ≤ 1) ∧
      (y ∈ (nestedReferenceBallChart d).boundary ↔ A = 1) := by
    simpa only [hsum, hres] using (nestedReferenceBallChart_regions d).2.2.2 y
  exact ⟨hregions.2.1.trans halgebra.1, hregions.1.trans halgebra.2.1,
    hregions.2.2.trans halgebra.2.2⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
