import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.ChartLineCrossings
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.EdgeIntersections
import PoincareConjecture.Proofs.M76.Mathlib.SegmentSubdivision
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional











set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex



theorem refined_edge_neighbor_parameters
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (Q : SimplicialComplex ℝ E) {a b q u v : E} (hab : a ≠ b)
    (hspace : Q.space ⊆ segment ℝ a b)
    (hquedge : {q, u} ∈ Q.faces) (hqvedge : {q, v} ∈ Q.faces)
    (hqu : q ≠ u) (hqv : q ≠ v) (huv : u ≠ v)
    (r : I) (hqr : AffineMap.lineMap a b (r : ℝ) = q) :
    ∃ s t : I, AffineMap.lineMap a b (s : ℝ) = u ∧
      AffineMap.lineMap a b (t : ℝ) = v ∧
      (((s : ℝ) < r ∧ (r : ℝ) < t) ∨ ((t : ℝ) < r ∧ (r : ℝ) < s)) := by
  have hqQ : q ∈ Q.space := Q.convexHull_subset_space hquedge
    (subset_convexHull ℝ _ (by simp))
  have huQ : u ∈ Q.space := Q.convexHull_subset_space hquedge
    (subset_convexHull ℝ _ (by simp))
  have hvQ : v ∈ Q.space := Q.convexHull_subset_space hqvedge
    (subset_convexHull ℝ _ (by simp))
  have hspan (x : E) (hx : x ∈ Q.space) : x ∈ affineSpan ℝ ({a, b} : Set E) := by
    apply convexHull_subset_affineSpan
    simpa only [convexHull_pair] using hspace hx
  have hcol : Collinear ℝ ({u, q, v} : Set E) :=
    collinear_triple_of_mem_affineSpan_pair (hspan u huQ) (hspan q hqQ) (hspan v hvQ)
  have hpair : ({u, q} : Finset E) ≠ {q, v} := by
    intro he
    have hu : u ∈ ({q, v} : Finset E) := he ▸ (by simp : u ∈ ({u, q} : Finset E))
    have huv' : u = v := by simpa [hqu.symm] using hu
    exact huv huv'
  have hinter : segment ℝ u q ∩ segment ℝ q v ⊆ {q} := by
    intro x hx
    have h := Q.mem_segment_inter_of_distinct_edges
      (by simpa only [Finset.pair_comm] using hquedge) hqvedge hpair hx
    rcases h.1 with rfl | hxq
    · exact (huv (h.2.resolve_left hqu.symm)).elim
    · exact hxq
  have hbetween := hcol.sbtw_of_segment_inter_subset hqu.symm hqv.symm hinter
  obtain ⟨s, hs, hsu⟩ := (segment_eq_image_lineMap ℝ a b).subset (hspace huQ)
  obtain ⟨t, ht, htv⟩ := (segment_eq_image_lineMap ℝ a b).subset (hspace hvQ)
  have hparam : Sbtw ℝ s (r : ℝ) t := by
    apply (AffineMap.lineMap_injective ℝ hab).sbtw_map_iff.mp
    rw [hsu, hqr, htv]
    exact hbetween
  have hrst := hparam.wbtw.mem_segment
  rw [segment_eq_uIcc, mem_uIcc] at hrst
  refine ⟨⟨s, hs⟩, ⟨t, ht⟩, hsu, htv, ?_⟩
  rcases hrst with ⟨hsr, hrt⟩ | ⟨htr, hrs⟩
  · exact Or.inl ⟨lt_of_le_of_ne hsr hparam.ne_left.symm,
      lt_of_le_of_ne hrt hparam.ne_right⟩
  · exact Or.inr ⟨lt_of_le_of_ne htr hparam.ne_right.symm,
      lt_of_le_of_ne hrs hparam.ne_left⟩



theorem refined_crossing_neighbor_signs
    {E X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : SimplicialComplex ℝ E) {a b q u v : E} (hab : a ≠ b)
    (hspace : Q.space ⊆ segment ℝ a b)
    (hquedge : {q, u} ∈ Q.faces) (hqvedge : {q, v} ∈ Q.faces)
    (hqu : q ≠ u) (hqv : q ≠ v) (huv : u ≠ v)
    (r : I) (hqr : AffineMap.lineMap a b (r : ℝ) = q)
    (B : OpenPartialHomeomorph X V) (g : E → X) (ell : V →ᴬ[ℝ] ℝ)
    (hline : ∀ t : I, B (g (AffineMap.lineMap a b (t : ℝ))) =
      AffineMap.lineMap (B (g a)) (B (g b)) (t : ℝ))
    (ha : ell (B (g a)) ≠ 0) (hb : ell (B (g b)) ≠ 0) (hq : ell (B (g q)) = 0) :
    (ell (B (g u)) < 0 ∧ 0 < ell (B (g v))) ∨
      (ell (B (g v)) < 0 ∧ 0 < ell (B (g u))) := by
  obtain ⟨s, t, hsu, htv, horder⟩ :=
    Q.refined_edge_neighbor_parameters hab hspace hquedge hqvedge hqu hqv huv r hqr
  have hheight (z : I) : ell (B (g (AffineMap.lineMap a b (z : ℝ)))) =
      AffineMap.lineMap (ell (B (g a))) (ell (B (g b))) (z : ℝ) := by
    rw [hline]
    exact ell.toAffineMap.apply_lineMap _ _ _
  have hrzero : AffineMap.lineMap (ell (B (g a))) (ell (B (g b))) (r : ℝ) = 0 := by
    rw [← hheight, hqr, hq]
  rcases AffineMap.lineMap_zero_alternative ha hb with hnone |
      ⟨r', _, _, _, hop, hzero, hbefore, hafter⟩
  · exact (hnone r hrzero).elim
  · have hrr : (r : ℝ) = (r' : ℝ) := (hzero r).mp hrzero
    have hsuheight := hheight s
    have htvheight := hheight t
    rw [hsu] at hsuheight
    rw [htv] at htvheight
    rcases horder with ⟨hsr, hrt⟩ | ⟨htr, hrs⟩
    · have hU := hbefore s (hrr ▸ hsr)
      have hV := hafter t (hrr ▸ hrt)
      rw [← hsuheight] at hU
      rw [← htvheight] at hV
      rcases hop with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact Or.inl ⟨neg_of_mul_pos_right hU ha.le, pos_of_mul_pos_right hV hb.le⟩
      · exact Or.inr ⟨neg_of_mul_pos_right hV hb.le, pos_of_mul_pos_right hU ha.le⟩
    · have hV := hbefore t (hrr ▸ htr)
      have hU := hafter s (hrr ▸ hrs)
      rw [← htvheight] at hV
      rw [← hsuheight] at hU
      rcases hop with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact Or.inr ⟨neg_of_mul_pos_right hV ha.le, pos_of_mul_pos_right hU hb.le⟩
      · exact Or.inl ⟨neg_of_mul_pos_right hU hb.le, pos_of_mul_pos_right hV ha.le⟩

end Geometry.SimplicialComplex

namespace OpenPartialHomeomorph



theorem same_domain_height_signs
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B C : OpenPartialHomeomorph X V) (ell m : V →ᴬ[ℝ] ℝ) {N F : Set X}
    (hBN : ∀ x ∈ B.source, x ∈ N ↔ 0 ≤ ell (B x))
    (hBF : ∀ x ∈ B.source, x ∈ F ↔ ell (B x) = 0)
    (hCN : ∀ x ∈ C.source, x ∈ N ↔ 0 ≤ m (C x))
    (hCF : ∀ x ∈ C.source, x ∈ F ↔ m (C x) = 0)
    {x : X} (hxB : x ∈ B.source) (hxC : x ∈ C.source) :
    (ell (B x) < 0 ↔ m (C x) < 0) ∧
      (ell (B x) = 0 ↔ m (C x) = 0) ∧ (0 < ell (B x) ↔ 0 < m (C x)) := by
  have hn : 0 ≤ ell (B x) ↔ 0 ≤ m (C x) := (hBN x hxB).symm.trans (hCN x hxC)
  have hz : ell (B x) = 0 ↔ m (C x) = 0 := (hBF x hxB).symm.trans (hCF x hxC)
  refine ⟨?_, hz, ?_⟩
  · simpa only [not_le] using hn.not
  · constructor
    · intro h
      exact lt_of_le_of_ne (hn.mp h.le) (fun he => h.ne' (hz.mpr he.symm))
    · intro h
      exact lt_of_le_of_ne (hn.mpr h.le) (fun he => h.ne' (hz.mp he.symm))

end OpenPartialHomeomorph
