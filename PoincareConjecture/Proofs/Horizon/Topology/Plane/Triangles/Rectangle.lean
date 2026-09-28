


import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Between









set_option autoImplicit false

open Set
open scoped Matrix Convex

namespace Poincare.Topology.Plane.Triangles

noncomputable section

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

variable {a b c d : ℝ}

private theorem lower_independent (hab : a < b) (hcd : c < d) :
    AffineIndependent ℝ (![!₂[a, c], !₂[b, c], !₂[b, d]] : Fin 3 → E2) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hsum i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hsum
  have h0 := congrArg (fun z : E2 => z 0) hsum
  have h1 := congrArg (fun z : E2 => z 1) hsum
  simp [Fin.sum_univ_succ] at hw h0 h1
  have hw2 : w 2 = 0 := by
    apply (mul_eq_zero.mp (show w 2 * (d - c) = 0 by
      nlinarith [congrArg (fun q : ℝ => q * c) hw])).resolve_right
    exact sub_ne_zero.mpr (ne_of_gt hcd)
  have hw0 : w 0 = 0 := by
    apply (mul_eq_zero.mp (show w 0 * (a - b) = 0 by
      nlinarith [congrArg (fun q : ℝ => q * b) hw])).resolve_right
    exact sub_ne_zero.mpr (ne_of_lt hab)
  fin_cases i <;> simp_all

private theorem upper_independent (hab : a < b) (hcd : c < d) :
    AffineIndependent ℝ (![!₂[a, c], !₂[a, d], !₂[b, d]] : Fin 3 → E2) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hsum i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hsum
  have h0 := congrArg (fun z : E2 => z 0) hsum
  have h1 := congrArg (fun z : E2 => z 1) hsum
  simp [Fin.sum_univ_succ] at hw h0 h1
  have hw2 : w 2 = 0 := by
    apply (mul_eq_zero.mp (show w 2 * (b - a) = 0 by
      nlinarith [congrArg (fun q : ℝ => q * a) hw])).resolve_right
    exact sub_ne_zero.mpr (ne_of_gt hab)
  have hw0 : w 0 = 0 := by
    apply (mul_eq_zero.mp (show w 0 * (c - d) = 0 by
      nlinarith [congrArg (fun q : ℝ => q * d) hw])).resolve_right
    exact sub_ne_zero.mpr (ne_of_lt hcd)
  fin_cases i <;> simp_all


def rectangleLowerBasis (hab : a < b) (hcd : c < d) : AffineBasis (Fin 3) ℝ E2 :=
  ⟨![!₂[a, c], !₂[b, c], !₂[b, d]], lower_independent hab hcd,
    (lower_independent hab hcd).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp [E2, finrank_euclideanSpace])⟩


def rectangleUpperBasis (hab : a < b) (hcd : c < d) : AffineBasis (Fin 3) ℝ E2 :=
  ⟨![!₂[a, c], !₂[a, d], !₂[b, d]], upper_independent hab hcd,
    (upper_independent hab hcd).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp [E2, finrank_euclideanSpace])⟩

@[simp] theorem rectangleLowerBasis_apply (hab : a < b) (hcd : c < d) (i : Fin 3) :
    rectangleLowerBasis hab hcd i = ![!₂[a, c], !₂[b, c], !₂[b, d]] i := rfl

@[simp] theorem rectangleUpperBasis_apply (hab : a < b) (hcd : c < d) (i : Fin 3) :
    rectangleUpperBasis hab hcd i = ![!₂[a, c], !₂[a, d], !₂[b, d]] i := rfl

private theorem coord_eq_of_combination (B : AffineBasis (Fin 3) ℝ E2)
    (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) {z : E2}
    (hz : ∑ i, w i • B i = z) (i : Fin 3) : B.coord i z = w i := by
  rw [← Finset.affineCombination_eq_linear_combination _ _ _ hw] at hz
  rw [← hz]
  exact B.coord_apply_combination_of_mem (Finset.mem_univ i) hw


theorem rectangleLowerBasis_coord (hab : a < b) (hcd : c < d) (z : E2) (i : Fin 3) :
    (rectangleLowerBasis hab hcd).coord i z =
      ![1 - (z 0 - a) / (b - a),
        (z 0 - a) / (b - a) - (z 1 - c) / (d - c),
        (z 1 - c) / (d - c)] i := by
  apply coord_eq_of_combination
  · simp [Fin.sum_univ_succ]
  · ext j
    fin_cases j <;> simp [Fin.sum_univ_succ] <;>
      field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt (sub_pos.mpr hcd)] <;> ring


theorem rectangleUpperBasis_coord (hab : a < b) (hcd : c < d) (z : E2) (i : Fin 3) :
    (rectangleUpperBasis hab hcd).coord i z =
      ![1 - (z 1 - c) / (d - c),
        (z 1 - c) / (d - c) - (z 0 - a) / (b - a),
        (z 0 - a) / (b - a)] i := by
  apply coord_eq_of_combination
  · simp [Fin.sum_univ_succ]
  · ext j
    fin_cases j <;> simp [Fin.sum_univ_succ] <;>
      field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt (sub_pos.mpr hcd)] <;> ring


theorem mem_rectangleLowerBasis_convexHull (hab : a < b) (hcd : c < d) (z : E2) :
    z ∈ convexHull ℝ (range (rectangleLowerBasis hab hcd)) ↔
      0 ≤ (z 1 - c) / (d - c) ∧
      (z 1 - c) / (d - c) ≤ (z 0 - a) / (b - a) ∧
      (z 0 - a) / (b - a) ≤ 1 := by
  rw [AffineBasis.convexHull_eq_nonneg_coord]
  simp only [mem_ofPred_eq, rectangleLowerBasis_coord, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero,
    and_true]
  constructor <;> intro h <;> rcases h with ⟨h0, h1, h2⟩ <;> constructor <;> try linarith
  all_goals constructor <;> linarith


theorem mem_rectangleUpperBasis_convexHull (hab : a < b) (hcd : c < d) (z : E2) :
    z ∈ convexHull ℝ (range (rectangleUpperBasis hab hcd)) ↔
      0 ≤ (z 0 - a) / (b - a) ∧
      (z 0 - a) / (b - a) ≤ (z 1 - c) / (d - c) ∧
      (z 1 - c) / (d - c) ≤ 1 := by
  rw [AffineBasis.convexHull_eq_nonneg_coord]
  simp only [mem_ofPred_eq, rectangleUpperBasis_coord, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero,
    and_true]
  constructor <;> intro h <;> rcases h with ⟨h0, h1, h2⟩ <;> constructor <;> try linarith
  all_goals constructor <;> linarith

private theorem normalized_mem_Icc_iff (hab : a < b) (x : ℝ) :
    (x - a) / (b - a) ∈ Icc (0 : ℝ) 1 ↔ x ∈ Icc a b := by
  simp only [mem_Icc, le_div_iff₀ (sub_pos.mpr hab),
    div_le_iff₀ (sub_pos.mpr hab), zero_mul, one_mul]
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith


theorem rectangle_triangle_union (hab : a < b) (hcd : c < d) :
    convexHull ℝ (range (rectangleLowerBasis hab hcd)) ∪
      convexHull ℝ (range (rectangleUpperBasis hab hcd)) =
      {z : E2 | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} := by
  ext z
  simp only [mem_union, mem_ofPred_eq, mem_rectangleLowerBasis_convexHull,
    mem_rectangleUpperBasis_convexHull]
  rw [← normalized_mem_Icc_iff hab, ← normalized_mem_Icc_iff hcd]
  simp only [mem_Icc]
  constructor
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) <;>
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    rcases le_total ((z 1 - c) / (d - c)) ((z 0 - a) / (b - a)) with h | h
    · exact Or.inl ⟨hy0, h, hx1⟩
    · exact Or.inr ⟨hx0, h, hy1⟩


theorem rectangle_triangle_inter (hab : a < b) (hcd : c < d) :
    convexHull ℝ (range (rectangleLowerBasis hab hcd)) ∩
      convexHull ℝ (range (rectangleUpperBasis hab hcd)) =
      affineSegment ℝ (!₂[a, c] : E2) !₂[b, d] := by
  rw [affineSegment_eq_segment]
  apply Subset.antisymm
  · intro z hz
    obtain ⟨hy0, hyx, hx1⟩ := (mem_rectangleLowerBasis_convexHull hab hcd z).mp hz.1
    obtain ⟨hx0, hxy, hy1⟩ := (mem_rectangleUpperBasis_convexHull hab hcd z).mp hz.2
    have heq := le_antisymm hxy hyx
    rw [segment_eq_image]
    refine ⟨(z 0 - a) / (b - a), ⟨hx0, hx1⟩, ?_⟩
    have hX : (z 0 - a) / (b - a) * (b - a) = z 0 - a :=
      div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hab))
    have hY : (z 0 - a) / (b - a) * (d - c) = z 1 - c := by
      rw [heq]
      exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hcd))
    ext i
    fin_cases i <;> simp <;> nlinarith
  · intro z hz
    constructor
    · exact segment_subset_convexHull
        (show (!₂[a, c] : E2) ∈ range (rectangleLowerBasis hab hcd) from ⟨0, rfl⟩)
        (show (!₂[b, d] : E2) ∈ range (rectangleLowerBasis hab hcd) from ⟨2, rfl⟩) hz
    · exact segment_subset_convexHull
        (show (!₂[a, c] : E2) ∈ range (rectangleUpperBasis hab hcd) from ⟨0, rfl⟩)
        (show (!₂[b, d] : E2) ∈ range (rectangleUpperBasis hab hcd) from ⟨2, rfl⟩) hz


theorem rectangle_triangle_diagonal_parametrization (hab : a < b) (hcd : c < d) :
    (fun t : ℝ =>
      rectangleLowerBasis hab hcd (Fin.succAbove (1 : Fin 3) 0) +
        t • (rectangleLowerBasis hab hcd (Fin.succAbove (1 : Fin 3) 1) -
          rectangleLowerBasis hab hcd (Fin.succAbove (1 : Fin 3) 0))) =
    (fun t : ℝ =>
      rectangleUpperBasis hab hcd (Fin.succAbove (1 : Fin 3) 0) +
        t • (rectangleUpperBasis hab hcd (Fin.succAbove (1 : Fin 3) 1) -
          rectangleUpperBasis hab hcd (Fin.succAbove (1 : Fin 3) 0))) := rfl

end

end Poincare.Topology.Plane.Triangles
