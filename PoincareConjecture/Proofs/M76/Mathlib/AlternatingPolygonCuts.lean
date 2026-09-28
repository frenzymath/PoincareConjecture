import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals

set_option autoImplicit false

open Set AffineMap

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

noncomputable def midpointSubdivision (P : Polygon E n) : Polygon E (n * 2) :=
  P.subdivide (fun j : Fin 3 => (j.val : ℝ) / 2)

private theorem midpointParameters_strictMono :
    StrictMono (fun j : Fin 3 => (j.val : ℝ) / 2) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  exact_mod_cast hij

theorem midpointSubdivision_apply_zero (P : Polygon E n) (i : Fin n) :
    P.midpointSubdivision (finProdFinEquiv (i, (0 : Fin 2))) = P i := by
  change P.subdivide _ _ = _
  rw [P.subdivide_apply]
  norm_num

theorem midpointSubdivision_apply_one (P : Polygon E n) (i : Fin n) :
    P.midpointSubdivision (finProdFinEquiv (i, (1 : Fin 2))) =
      lineMap (P i) (P (finRotate n i)) (1 / 2 : ℝ) := by
  change P.subdivide _ _ = _
  rw [P.subdivide_apply]
  norm_num

theorem midpoint_rotate_zero (i : Fin n) :
    finRotate (n * 2) (finProdFinEquiv (i, (0 : Fin 2))) =
      finProdFinEquiv (i, (1 : Fin 2)) := by
  simpa using finRotate_finProdFinEquiv_castSucc i (0 : Fin 1)

theorem midpoint_rotate_one (i : Fin n) :
    finRotate (n * 2) (finProdFinEquiv (i, (1 : Fin 2))) =
      finProdFinEquiv (finRotate n i, (0 : Fin 2)) := by
  simpa using finRotate_finProdFinEquiv_last (m := 1) i

theorem midpointSubdivision_boundary (P : Polygon E n) :
    P.midpointSubdivision.boundary ℝ = P.boundary ℝ := by
  exact P.subdivide_boundary _ midpointParameters_strictMono (by norm_num) (by norm_num)

theorem midpointSubdivision_simple (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    P.midpointSubdivision.HasSimplicialEdges ∧
      Function.Injective P.midpointSubdivision := by
  exact ⟨P.hasSimplicialEdges_subdivide hP hinj _ midpointParameters_strictMono
    (by norm_num) (by norm_num),
    P.injective_subdivide hP hinj _ midpointParameters_strictMono (by norm_num) (by norm_num)⟩

def midpointCutParameters (α β : Fin n → ℝ) : Fin (n * 2) → ℝ := fun k =>
  let ij := finProdFinEquiv.symm k
  if ij.2 = 0 then 2 * α ij.1 else 2 * β ij.1 - 1

theorem midpointCutParameters_zero (α β : Fin n → ℝ) (i : Fin n) :
    midpointCutParameters α β (finProdFinEquiv (i, (0 : Fin 2))) = 2 * α i := by
  simp [midpointCutParameters]

theorem midpointCutParameters_one (α β : Fin n → ℝ) (i : Fin n) :
    midpointCutParameters α β (finProdFinEquiv (i, (1 : Fin 2))) = 2 * β i - 1 := by
  simp [midpointCutParameters]

theorem midpointCutParameters_mem (α β : Fin n → ℝ)
    (hα : ∀ i, α i ∈ Ioo (0 : ℝ) (1 / 2))
    (hβ : ∀ i, β i ∈ Ioo (1 / 2 : ℝ) 1) :
    ∀ k, midpointCutParameters α β k ∈ Ioo (0 : ℝ) 1 := by
  intro k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  fin_cases j
  · simpa [midpointCutParameters] using
      (show 2 * α i ∈ Ioo (0 : ℝ) 1 from
        ⟨by linarith [(hα i).1], by linarith [(hα i).2]⟩)
  · simpa [midpointCutParameters] using
      (show 2 * β i - 1 ∈ Ioo (0 : ℝ) 1 from
        ⟨by linarith [(hβ i).1], by linarith [(hβ i).2]⟩)

theorem midpointSubdivision_edgeCut_zero (P : Polygon E n)
    (α β : Fin n → ℝ) (i : Fin n) :
    P.midpointSubdivision.edgeCut (midpointCutParameters α β)
        (finProdFinEquiv (i, (0 : Fin 2))) = P.edgeCut α i := by
  unfold edgeCut
  rw [midpoint_rotate_zero, midpointSubdivision_apply_zero,
    midpointSubdivision_apply_one, midpointCutParameters_zero, lineMap_lineMap_right]
  congr 1
  ring

theorem midpointSubdivision_edgeCut_one (P : Polygon E n)
    (α β : Fin n → ℝ) (i : Fin n) :
    P.midpointSubdivision.edgeCut (midpointCutParameters α β)
        (finProdFinEquiv (i, (1 : Fin 2))) = P.edgeCut β i := by
  unfold edgeCut
  rw [midpoint_rotate_one, midpointSubdivision_apply_one,
    midpointSubdivision_apply_zero, midpointCutParameters_one, lineMap_lineMap_left]
  congr 1
  ring

private theorem original_segment_image (a b : E) {u v : ℝ} (huv : u ≤ v) :
    segment ℝ (lineMap a b u) (lineMap a b v) = lineMap a b '' Icc u v := by
  rw [← image_segment ℝ, segment_eq_Icc huv]

theorem midpointSubdivision_cutArc_zero (P : Polygon E n)
    (α β : Fin n → ℝ) (hα : ∀ i, α i ∈ Ioo (0 : ℝ) (1 / 2))
    (hβ : ∀ i, β i ∈ Ioo (1 / 2 : ℝ) 1) (i : Fin n) :
    P.midpointSubdivision.cutArc (midpointCutParameters α β)
        (finProdFinEquiv (i, (0 : Fin 2))) =
      segment ℝ (P.edgeCut α i) (P.edgeCut β i) := by
  have ht (k) : midpointCutParameters α β k ∈ Icc (0 : ℝ) 1 :=
    ⟨(midpointCutParameters_mem α β hα hβ k).1.le,
      (midpointCutParameters_mem α β hα hβ k).2.le⟩
  rw [cutArc_eq_segments _ _ ht, midpoint_rotate_zero,
    midpointSubdivision_edgeCut_zero, midpointSubdivision_apply_one,
    midpointSubdivision_edgeCut_one]
  change segment ℝ (lineMap _ _ (α i)) (lineMap _ _ (1 / 2 : ℝ)) ∪
    segment ℝ (lineMap _ _ (1 / 2 : ℝ)) (lineMap _ _ (β i)) =
      segment ℝ (lineMap _ _ (α i)) (lineMap _ _ (β i))
  rw [original_segment_image _ _ (hα i).2.le,
    original_segment_image _ _ (hβ i).1.le,
    original_segment_image _ _ ((hα i).2.trans (hβ i).1).le,
    ← image_union, Icc_union_Icc_eq_Icc (hα i).2.le (hβ i).1.le]

theorem midpointSubdivision_cutArc_one (P : Polygon E n)
    (α β : Fin n → ℝ) (hα : ∀ i, α i ∈ Ioo (0 : ℝ) (1 / 2))
    (hβ : ∀ i, β i ∈ Ioo (1 / 2 : ℝ) 1) (i : Fin n) :
    P.midpointSubdivision.cutArc (midpointCutParameters α β)
        (finProdFinEquiv (i, (1 : Fin 2))) =
      (lineMap (P i) (P (finRotate n i)) '' Icc (β i) 1) ∪
        (lineMap (P (finRotate n i)) (P (finRotate n (finRotate n i))) ''
          Icc 0 (α (finRotate n i))) := by
  have ht (k) : midpointCutParameters α β k ∈ Icc (0 : ℝ) 1 :=
    ⟨(midpointCutParameters_mem α β hα hβ k).1.le,
      (midpointCutParameters_mem α β hα hβ k).2.le⟩
  rw [cutArc_eq_segments _ _ ht, midpoint_rotate_one,
    midpointSubdivision_edgeCut_one, midpointSubdivision_apply_zero,
    midpointSubdivision_edgeCut_zero]
  have htail := original_segment_image (P i) (P (finRotate n i)) (hβ i).2.le
  have hhead := original_segment_image (P (finRotate n i))
    (P (finRotate n (finRotate n i))) (hα (finRotate n i)).1.le
  simpa only [lineMap_apply_one, lineMap_apply_zero, edgeCut] using
    congrArg₂ (· ∪ ·) htail hhead

end Polygon
