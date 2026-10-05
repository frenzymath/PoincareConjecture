import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.PlanarCornerCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.PlanarSegmentLocalModel
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.SegmentSubdivision

/-!
# Local line models for planar corners

An independent corner is an affine image of the absolute-value
graph. A collinear corner with exact endpoint intersection is
already a segment. See Erickson, Simple Polygons, pp. 2--3
and M76 derivation 98.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

/-- An independent planar corner has an ambient straight-line
model near its center. See Erickson pp. 2--3 and M76 derivation 98. -/
theorem AffineIndependent.exists_local_line_segments {a b c : ℝ × ℝ}
    (h : AffineIndependent ℝ ![a, b, c]) :
    ∃ e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (e b).2 = 0 ∧
      ∀ᶠ x in 𝓝 b, x ∈ segment ℝ a b ∪ segment ℝ b c ↔ (e x).2 = 0 := by
  obtain ⟨f, ha, hb, hc⟩ := h.exists_planar_corner_coordinates
  let s := Homeomorph.subContinuousGraph (abs : ℝ → ℝ) continuous_abs
  let e := f.toHomeomorph.trans s
  have hmap (x : ℝ × ℝ) :
      x ∈ segment ℝ a b ∪ segment ℝ b c ↔
        f x ∈ segment ℝ (-1, 1) (0, 0) ∪ segment ℝ (0, 0) (1, 1) := by
    have hab : f '' segment ℝ a b = segment ℝ (f a) (f b) :=
      image_segment ℝ f.toAffineEquiv.toAffineMap a b
    have hbc : f '' segment ℝ b c = segment ℝ (f b) (f c) :=
      image_segment ℝ f.toAffineEquiv.toAffineMap b c
    rw [← ha, ← hb, ← hc, ← hab, ← hbc, ← image_union]
    exact f.injective.mem_set_image.symm
  refine ⟨e, ?_, ?_⟩
  · change (f b).2 - |(f b).1| = 0
    simp [hb]
  · have hnhds : ∀ᶠ x in 𝓝 b, |(f x).1| < 1 :=
      (isOpen_lt (continuous_abs.comp (continuous_fst.comp f.continuous))
        continuous_const).mem_nhds (by simp [hb])
    filter_upwards [hnhds] with x hx
    rw [hmap x, mem_reference_corner_iff hx]
    exact (Homeomorph.subContinuousGraph_snd_eq_zero_iff abs continuous_abs (f x)).symm

/-- Two nondegenerate planar segments meeting only at their shared
endpoint have a local ambient line model there. Collinear triples
are included. See Erickson pp. 2--3 and M76 derivation 98. -/
theorem exists_local_line_of_segment_corner {a b c : ℝ × ℝ}
    (hab : a ≠ b) (hcb : c ≠ b)
    (hinter : segment ℝ a b ∩ segment ℝ b c ⊆ {b}) :
    ∃ e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (e b).2 = 0 ∧
      ∀ᶠ x in 𝓝 b, x ∈ segment ℝ a b ∪ segment ℝ b c ↔ (e x).2 = 0 := by
  by_cases h : AffineIndependent ℝ ![a, b, c]
  · exact h.exists_local_line_segments
  · have hc : Collinear ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
      simpa only [affineIndependent_iff_not_collinear_set, not_not] using h
    have hb := hc.sbtw_of_segment_inter_subset hab hcb hinter
    rw [hb.wbtw.segment_union]
    exact PlanarSegment.exists_local_line hb.wbtw.mem_segment hab.symm hcb.symm
