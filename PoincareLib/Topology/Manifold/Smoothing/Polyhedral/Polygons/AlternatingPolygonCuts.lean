import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonCutArcIntervals

/-!
# Original event vertices alternating with edge midpoints

One midpoint subdivision gives exact cyclic labels for the
fixed event bodies and the original triangle connectors.
The two original cuts on each edge keep their actual points
and their entire original connecting arcs. See Alexander 1924,
pp. 6--8, Hudson 1969, pp. 12--19 and M76 derivation 313.
-/

set_option autoImplicit false

open Set AffineMap

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Subdivision at the unchanged original vertices and edge
midpoints. The product index retains each original edge.
See Alexander pp. 6--8 and M76 derivation 313. -/
noncomputable def midpointSubdivision (P : Polygon E n) : Polygon E (n * 2) :=
  P.subdivide (fun j : Fin 3 => (j.val : ℝ) / 2)

private theorem midpointParameters_strictMono :
    StrictMono (fun j : Fin 3 => (j.val : ℝ) / 2) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  exact_mod_cast hij

/-- The first vertex in each block is its unchanged original
vertex. See M76 derivation 313. -/
theorem midpointSubdivision_apply_zero (P : Polygon E n) (i : Fin n) :
    P.midpointSubdivision (finProdFinEquiv (i, (0 : Fin 2))) = P i := by
  change P.subdivide _ _ = _
  rw [P.subdivide_apply]
  norm_num

/-- The second vertex is the midpoint of the same original
edge. See M76 derivation 313. -/
theorem midpointSubdivision_apply_one (P : Polygon E n) (i : Fin n) :
    P.midpointSubdivision (finProdFinEquiv (i, (1 : Fin 2))) =
      lineMap (P i) (P (finRotate n i)) (1 / 2 : ℝ) := by
  change P.subdivide _ _ = _
  rw [P.subdivide_apply]
  norm_num

/-- Rotation from an original vertex reaches its unchanged
edge midpoint. See M76 derivation 313. -/
theorem midpoint_rotate_zero (i : Fin n) :
    finRotate (n * 2) (finProdFinEquiv (i, (0 : Fin 2))) =
      finProdFinEquiv (i, (1 : Fin 2)) := by
  simpa using finRotate_finProdFinEquiv_castSucc i (0 : Fin 1)

/-- Rotation from a midpoint reaches the next original vertex,
including the closing edge. See M76 derivation 313. -/
theorem midpoint_rotate_one (i : Fin n) :
    finRotate (n * 2) (finProdFinEquiv (i, (1 : Fin 2))) =
      finProdFinEquiv (finRotate n i, (0 : Fin 2)) := by
  simpa using finRotate_finProdFinEquiv_last (m := 1) i

/-- Midpoint subdivision preserves the complete original
boundary, including degenerate polygons. See derivation 313. -/
theorem midpointSubdivision_boundary (P : Polygon E n) :
    P.midpointSubdivision.boundary ℝ = P.boundary ℝ := by
  exact P.subdivide_boundary _ midpointParameters_strictMono (by norm_num) (by norm_num)

/-- An original simple simplicial polygon stays simple after
inserting exactly its edge midpoints. See Hudson pp. 12--19
and M76 derivation 313. -/
theorem midpointSubdivision_simple (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    P.midpointSubdivision.HasSimplicialEdges ∧
      Function.Injective P.midpointSubdivision := by
  exact ⟨P.hasSimplicialEdges_subdivide hP hinj _ midpointParameters_strictMono
    (by norm_num) (by norm_num),
    P.injective_subdivide hP hinj _ midpointParameters_strictMono (by norm_num) (by norm_num)⟩

/-- The original two edge cuts, expressed on the two unchanged
half edges. See M76 derivation 313. -/
def midpointCutParameters (α β : Fin n → ℝ) : Fin (n * 2) → ℝ := fun k =>
  let ij := finProdFinEquiv.symm k
  if ij.2 = 0 then 2 * α ij.1 else 2 * β ij.1 - 1

/-- The first half-edge parameter represents the original
left mark. See M76 derivation 313. -/
theorem midpointCutParameters_zero (α β : Fin n → ℝ) (i : Fin n) :
    midpointCutParameters α β (finProdFinEquiv (i, (0 : Fin 2))) = 2 * α i := by
  simp [midpointCutParameters]

/-- The second half-edge parameter represents the original
right mark. See M76 derivation 313. -/
theorem midpointCutParameters_one (α β : Fin n → ℝ) (i : Fin n) :
    midpointCutParameters α β (finProdFinEquiv (i, (1 : Fin 2))) = 2 * β i - 1 := by
  simp [midpointCutParameters]

/-- Strict cuts on opposite sides of the original midpoint
remain strict interior cuts after subdivision. See derivation 313. -/
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

/-- The first new cut is literally the original left mark.
No body membership has to be reselected. See derivation 313. -/
theorem midpointSubdivision_edgeCut_zero (P : Polygon E n)
    (α β : Fin n → ℝ) (i : Fin n) :
    P.midpointSubdivision.edgeCut (midpointCutParameters α β)
        (finProdFinEquiv (i, (0 : Fin 2))) = P.edgeCut α i := by
  unfold edgeCut
  rw [midpoint_rotate_zero, midpointSubdivision_apply_zero,
    midpointSubdivision_apply_one, midpointCutParameters_zero, lineMap_lineMap_right]
  congr 1
  ring

/-- The second new cut is literally the original right mark.
See M76 derivation 313. -/
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

/-- The full connector arc is exactly the original segment
between the two chosen marks. See Alexander pp. 6--8 and
M76 derivation 313. -/
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

/-- The full original-vertex arc keeps the previous edge tail
and the next edge head. The cyclic corner is unchanged.
See Alexander pp. 6--8 and M76 derivation 313. -/
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
