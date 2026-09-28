import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleApex
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ShortSegmentNeighborhood

set_option autoImplicit false

open Set Metric Geometry SignType

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

theorem exists_triangle_coface_sign_witness
    (p q : (T.marked 2).vertices) {s t : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 3)
    (hps : (p : T.index → ℝ × V3) ∈ s) (hqs : (q : T.index → ℝ × V3) ∈ s)
    (ht : t ∈ T.ambient.faces) (htcard : t.card = 4) (hst : s ⊆ t) :
    ∃ x ∈ convexHull ℝ (t : Set (T.index → ℝ × V3)),
      0 < T.height p x * T.height q x := by
  classical
  obtain ⟨v, _, hvt, hvD⟩ := T.exists_triangle_coface_apex hs hscard ht htcard hst
  have hpHull : (p : T.index → ℝ × V3) ∈ convexHull ℝ (t : Set _) :=
    subset_convexHull ℝ _ (hst hps)
  have hvHull : v ∈ convexHull ℝ (t : Set (T.index → ℝ × V3)) :=
    subset_convexHull ℝ _ (hvt ▸ Finset.mem_insert_self v s)
  have htp : t ∈ (T.ambient.closedStar p).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using ht⟩
  have htq : t ∈ (T.ambient.closedStar q).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hqs)] using ht⟩
  have hHullp := (T.ambient.closedStar p).convexHull_subset_space htp
  have hHullq := (T.ambient.closedStar q).convexHull_subset_space htq
  have htR := T.triangle_coface_mem_region hs hscard ht hst
  have hHullR := (T.marked 0).convexHull_subset_space htR
  have hpDisk := (T.marked 2).vertices_subset_space p.property
  have hpzero : T.height p p = 0 :=
    (T.height_eq_zero_iff p (hHullp hpHull) (hHullR hpHull)).mpr hpDisk
  have hvnonzero : T.height p v ≠ 0 :=
    fun h => hvD ((T.height_eq_zero_iff p (hHullp hvHull) (hHullR hvHull)).mp h)
  obtain ⟨hpParam, hjp⟩ := T.parameter_disk_point hpDisk
  let z : D := ⟨T.parameter p, hpParam⟩
  have hjz : j z = (T.inverse p : X) := hjp
  have hsource : j z ∈ (T.chart (T.chart_index p)).source ∩
      (T.chart (T.chart_index q)).source := by
    rw [hjz]
    exact ⟨T.star_source p (hHullp hpHull), T.star_source q (hHullq hpHull)⟩
  obtain ⟨V, hV, hzV, _, hsign⟩ :=
    T.overlap (T.chart_index p) (T.chart_index q) z hsource
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  have hzU : j z ∈ U := by
    change (⟨j z, T.disk_in_region z.property⟩ : R) ∈
      (Subtype.val : R → X) ⁻¹' U
    rwa [hUV]
  have hpU : (T.inverse p : X) ∈ U := hjz ▸ hzU
  have hg : ContinuousOn (fun x => (T.inverse x : X))
      (convexHull ℝ (t : Set (T.index → ℝ × V3))) :=
    (continuous_subtype_val.comp_continuousOn T.inverse_continuous).mono
      (T.ambient.convexHull_subset_space ht)
  obtain ⟨r, hr, hrU⟩ := hg.exists_short_segment_mem_open
    (convex_convexHull ℝ _) hpHull hvHull hU hpU
  let x := AffineMap.lineMap (p : T.index → ℝ × V3) v r
  have hxHull : x ∈ convexHull ℝ (t : Set (T.index → ℝ × V3)) :=
    (convex_convexHull ℝ _).segment_subset hpHull hvHull
      (lineMap_mem_segment ℝ _ _ ⟨hr.1.le, hr.2.le⟩)
  have hxK := T.ambient.convexHull_subset_space ht hxHull
  have hxR : (T.inverse x : X) ∈ R :=
    (T.inverse_mem_region_iff hxK).mpr (hHullR hxHull)
  have hxV : (⟨T.inverse x, hxR⟩ : R) ∈ V := by
    rw [← hUV]
    exact hrU
  have hsignx : sign (T.height p x) = sign (T.height q x) := hsign hxV
  obtain ⟨a, ha⟩ := T.height_affine p t htp
  have hxheight : T.height p x = r * T.height p v := by
    rw [ha hxHull]
    change a.toAffineMap (AffineMap.lineMap (p : T.index → ℝ × V3) v r) = _
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
    change (1 - r) * a p + r * a v = r * T.height p v
    rw [← ha hpHull, ← ha hvHull, hpzero, mul_zero, zero_add]
  have hxnonzero : T.height p x ≠ 0 := by
    rw [hxheight]
    exact mul_ne_zero hr.1.ne' hvnonzero
  refine ⟨x, hxHull, ?_⟩
  rcases lt_or_gt_of_ne hxnonzero with hneg | hpos
  · exact mul_pos_of_neg_of_neg hneg
      (sign_eq_neg_one_iff.mp (hsignx.symm.trans (sign_neg hneg)))
  · exact mul_pos hpos (sign_eq_one_iff.mp (hsignx.symm.trans (sign_pos hpos)))

end PoincareConjecture.M76.OriginalProperDiskTriangulation
