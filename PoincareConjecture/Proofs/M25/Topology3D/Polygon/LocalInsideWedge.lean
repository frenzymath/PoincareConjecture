import PoincareConjecture.Proofs.M25.Topology3D.Plane.PairCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CornerSectors
import PoincareConjecture.Proofs.M25.Topology3D.Plane.LocalRegionSides
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.LocalSides
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.RegionBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem IsSimplePolygon.exists_local_incident_segments {p : Polygon E n}
    (hp : IsSimplePolygon p) (k : Fin n) :
    ∃ U : Set E, IsOpen U ∧ p k ∈ U ∧ ∀ z ∈ U,
      z ∈ p.boundary ℝ ↔ z ∈ segment ℝ (p k) (p ((finRotate n).symm k)) ∪
        segment ℝ (p k) (p (finRotate n k)) := by
  classical
  let j := (finRotate n).symm k
  have hjk : finRotate n j = k := (finRotate n).apply_symm_apply k
  obtain ⟨U, hU, hkU, hlocal⟩ := exists_open_iUnion_eq_of_mem_imp
    (p.edgeSet ℝ) (fun i => (polygon_edgeSet_isCompact p i).isClosed) {j, k} (p k) (by
      intro i hi
      rcases (hp.vertex_mem_edgeSet_iff k i).mp hi with hki | hki
      · exact Or.inr hki.symm
      · exact Or.inl ((finRotate n).injective (hki.symm.trans hjk.symm)))
  have hsegj : segment ℝ (p k) (p j) = p.edgeSet ℝ j := by
    rw [polygon_edgeSet_eq_segment, hjk, segment_symm]
  have hsegk : segment ℝ (p k) (p (finRotate n k)) = p.edgeSet ℝ k :=
    (polygon_edgeSet_eq_segment p k).symm
  refine ⟨U, hU, hkU, ?_⟩
  intro z hz
  change z ∈ ⋃ i, p.edgeSet ℝ i ↔ _
  rw [hlocal z hz, hsegj, hsegk]
  simp only [mem_insert_iff, mem_singleton_iff, exists_eq_or_imp, exists_eq_left, mem_union]

theorem IsSimplePolygon.exists_local_inside_wedge [FiniteDimensional ℝ E]
    {p : Polygon E n} (hp : IsSimplePolygon p) (hdim : Module.finrank ℝ E = 2)
    (k : Fin n)
    (hli : LinearIndependent ℝ
      ![p ((finRotate n).symm k) - p k, p (finRotate n k) - p k])
    (X : E →L[ℝ] ℝ) (hX : Function.Surjective X)
    (hsupport : ∀ j, X (p k) ≤ X (p j)) :
    ∃ f : E ≃ᴬ[ℝ] (ℝ × ℝ),
      f (p k) = (0, 0) ∧ f (p ((finRotate n).symm k)) = (1, 0) ∧
      f (p (finRotate n k)) = (0, 1) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      f ⁻¹' (Ioo 0 r ×ˢ Ioo 0 r) ⊆ polygonInterior p ∧
      f ⁻¹' (Icc 0 r ×ˢ Icc 0 r) ⊆ closure (polygonInterior p) := by
  let q := p k
  let a := p ((finRotate n).symm k)
  let b := p (finRotate n k)
  obtain ⟨U, hU, hqU, hlocal⟩ := hp.exists_local_incident_segments k
  obtain ⟨f, hfq, hfa, hfb⟩ := exists_continuousAffineEquiv_map_triangle hdim hli
  change f q = (0, 0) at hfq
  change f a = (1, 0) at hfa
  change f b = (0, 1) at hfb
  have himage (c : E) : f '' segment ℝ q c = segment ℝ (0, 0) (f c) := by
    have hi := image_segment ℝ f.toAffineEquiv.toAffineMap q c
    change f '' segment ℝ q c = segment ℝ (f q) (f c) at hi
    simpa only [hfq] using hi
  have hmem (c z : E) : z ∈ segment ℝ q c ↔ f z ∈ segment ℝ (0, 0) (f c) := by
    rw [← himage]
    constructor
    · exact mem_image_of_mem f
    · rintro ⟨w, hw, hew⟩
      exact f.injective hew ▸ hw
  have hlocalf (z : E) (hz : z ∈ U) : z ∈ p.boundary ℝ ↔ f z ∈ unitCorner := by
    exact (hlocal z hz).trans (by
      simpa only [unitCorner, mem_union, hfa, hfb] using or_congr (hmem a z) (hmem b z))
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp (f.toHomeomorph.isOpenMap U hU) (0, 0)
    (by rw [← hfq]; exact mem_image_of_mem f hqU)
  let r := min ρ 1
  have hr : 0 < r := lt_min hρ zero_lt_one
  have hr1 : r ≤ 1 := min_le_right _ _
  let W0 : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) r
  let A0 : Set (ℝ × ℝ) := Ioo 0 r ×ˢ Ioo 0 r
  let B0 : Set (ℝ × ℝ) :=
    (Ioo (-r) 0 ×ˢ Ioo (-r) r) ∪ (Ioo (-r) r ×ˢ Ioo (-r) 0)
  have hsectors := unitCorner_box_sectors hr hr1
  change IsOpen W0 ∧ (0, 0) ∈ W0 ∧ IsPreconnected A0 ∧ IsPreconnected B0 ∧
    A0 ∪ B0 = W0 \ unitCorner at hsectors
  obtain ⟨hW0, h0W, hA0, hB0, hAB0⟩ := hsectors
  have hWball : W0 = ball (0, 0) r := by
    rw [← ball_prod_same, Real.ball_zero_eq_Ioo]
  have hWU : f ⁻¹' W0 ⊆ U := by
    intro z hz
    have him : f z ∈ f '' U := hρU
      (ball_subset_ball (min_le_left ρ 1) (hWball ▸ hz))
    obtain ⟨w, hw, hew⟩ := him
    exact f.injective hew ▸ hw
  have hAB : (f ⁻¹' A0) ∪ (f ⁻¹' B0) = (f ⁻¹' W0) \ p.boundary ℝ := by
    ext z
    change f z ∈ A0 ∪ B0 ↔ f z ∈ W0 ∧ z ∉ p.boundary ℝ
    rw [hAB0]
    constructor
    · rintro ⟨hz, hc⟩
      exact ⟨hz, fun hzC => hc ((hlocalf z (hWU hz)).mp hzC)⟩
    · rintro ⟨hz, hc⟩
      exact ⟨hz, fun hzC => hc ((hlocalf z (hWU hz)).mpr hzC)⟩
  have hu : 0 ≤ X (a - q) := by
    simpa only [map_sub, sub_nonneg] using hsupport ((finRotate n).symm k)
  have hv : 0 ≤ X (b - q) := by
    simpa only [map_sub, sub_nonneg] using hsupport (finRotate n k)
  have hpos : 0 < X (a - q) ∨ 0 < X (b - q) := by
    rcases lt_or_eq_of_le hu with h | h
    · exact Or.inl h
    rcases lt_or_eq_of_le hv with h' | h'
    · exact Or.inr h'
    have hspan : Submodule.span ℝ (range ![a - q, b - q]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by simp [hdim])
    have hker : Submodule.span ℝ (range ![a - q, b - q]) ≤ X.toLinearMap.ker := by
      apply Submodule.span_le.mpr
      rintro w ⟨i, rfl⟩
      fin_cases i
      · exact h.symm
      · exact h'.symm
    rw [hspan] at hker
    obtain ⟨w, hw⟩ := hX 1
    have hzero : X w = 0 := hker (Submodule.mem_top : w ∈ (⊤ : Submodule ℝ E))
    rw [hw] at hzero
    exact (one_ne_zero hzero).elim
  have hfline (c : E) (t : ℝ) :
      f (AffineMap.lineMap q c t) = AffineMap.lineMap (0, 0) (f c) t := by
    have h := f.toAffineEquiv.toAffineMap.apply_lineMap q c t
    change f (AffineMap.lineMap q c t) = AffineMap.lineMap (f q) (f c) t at h
    simpa only [hfq] using h
  have hline (c : E) (hc : 0 < X (c - q)) :
      X (AffineMap.lineMap q c (-r / 2)) < X q := by
    rw [AffineMap.lineMap_apply_module', map_add, map_smul]
    change (-r / 2) * X (c - q) + X q < X q
    have hneg : (-r / 2) * X (c - q) < 0 :=
      mul_neg_of_neg_of_pos (show -r / 2 < 0 by linarith) hc
    linarith
  have hBO : ((f ⁻¹' B0) ∩ polygonExterior p).Nonempty := by
    have hmid : -r < -r / 2 ∧ -r / 2 < 0 := by constructor <;> linarith
    have hneg : -r < 0 := neg_neg_of_pos hr
    rcases hpos with ha | hb
    · let z := AffineMap.lineMap q a (-r / 2)
      have hfz : f z = (-r / 2, 0) := by
        rw [hfline, hfa]
        ext <;> simp [AffineMap.lineMap_apply_module]
      refine ⟨z, ?_, polygonExterior_of_lt_vertex_bound p X hX (X q) hsupport (hline a ha)⟩
      change f z ∈ B0
      rw [hfz]
      exact Or.inl ⟨hmid, hneg, hr⟩
    · let z := AffineMap.lineMap q b (-r / 2)
      have hfz : f z = (0, -r / 2) := by
        rw [hfline, hfb]
        ext <;> simp [AffineMap.lineMap_apply_module]
      refine ⟨z, ?_, polygonExterior_of_lt_vertex_bound p X hX (X q) hsupport (hline b hb)⟩
      change f z ∈ B0
      rw [hfz]
      exact Or.inr ⟨⟨hneg, hr⟩, hmid⟩
  obtain ⟨hI, hO, _, _, hIO, hcover, _, _, hfront, _⟩ := hp.polygonRegions_spec hdim
  have hqfront : q ∈ frontier (polygonInterior p) := by
    rw [hfront]
    exact polygon_vertex_mem_boundary p k
  have hqW : q ∈ f ⁻¹' W0 := by
    change f q ∈ W0
    rw [hfq]
    exact h0W
  have hAI := (preconnected_local_sides_subset_regions hI hO hIO hcover
    (hW0.preimage f.continuous) hqW hqfront
    (f.toHomeomorph.isPreconnected_preimage.mpr hA0)
    (f.toHomeomorph.isPreconnected_preimage.mpr hB0) hAB hBO).1
  refine ⟨f, hfq, hfa, hfb, r, hr, hr1, hAI, ?_⟩
  have hclosure := closure_mono hAI
  rw [← f.toHomeomorph.preimage_closure] at hclosure
  change f ⁻¹' closure A0 ⊆ closure (polygonInterior p) at hclosure
  simpa only [A0, closure_prod_eq, closure_Ioo hr.ne] using hclosure

end PoincareConjecture.M25.Topology3D
