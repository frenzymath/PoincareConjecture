import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ResidualBand
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  [Fintype K.barycentricSubdivision.faces]

theorem residualBand_halfEdge_passage
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (v : K.vertices) (hv : v ∈ e.val) :
    residualBand K e ∩ segment ℝ (originalEdgeCentroid K e).val v.val =
        segment ℝ (originalEdgeCentroid K e).val (primalEdgeMark K e v) ∧
      residualBandRim K e ∩ segment ℝ (originalEdgeCentroid K e).val v.val =
        {primalEdgeMark K e v} := by
  have hadj := (originalVertexCentroid_adj_edgeCentroid K e v hv).symm
  have hface : ({(originalEdgeCentroid K e).val, (originalVertexCentroid K v).val} :
      Finset E) ∈ K.barycentricSubdivision.faces := by
    have hf := hadj.2
    change (({originalEdgeCentroid K e, originalVertexCentroid K v} :
      Finset K.barycentricSubdivision.vertices).map (Function.Embedding.subtype _)) ∈
      K.barycentricSubdivision.faces at hf
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hf
  have h := (K.barycentricSubdivision.vertexDualUnion_edge_passage
    {originalEdgeCentroid K e} (originalEdgeCentroid K e) (originalVertexCentroid K v)
    hadj.ne hface (by simp) (by simpa using Ne.symm hadj.ne)).2
  simpa only [K.barycentricSubdivision.vertexDualUnion_singleton,
    K.barycentricSubdivision.vertexDualRim_singleton, originalVertexCentroid_val,
    residualBand, residualBandRim, primalEdgeMark, Finset.pair_comm] using h

private theorem segment_lineMap_interval (a b : E) {u v : ℝ} (huv : u ≤ v) :
    segment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) =
      AffineMap.lineMap a b '' Icc u v := by
  rw [← image_segment ℝ (AffineMap.lineMap a b), segment_eq_Icc huv]

theorem residualBridge_eq_band_radii
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    residualBridge K e a b =
      segment ℝ (originalEdgeCentroid K e).val (primalEdgeMark K e a) ∪
        segment ℝ (originalEdgeCentroid K e).val (primalEdgeMark K e b) := by
  rw [residualBridge_eq_image K e heq, originalEdgeCentroid_val K e heq,
    primalEdgeMark_first_formula K e heq, primalEdgeMark_second_formula K e heq,
    segment_symm ℝ (AffineMap.lineMap a.val b.val (1 / 2 : ℝ)),
    segment_lineMap_interval _ _ (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2),
    segment_lineMap_interval _ _ (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4), ← image_union]
  congr 1
  ext t
  simp only [mem_Icc, mem_union]
  constructor
  · intro ht
    by_cases h : t ≤ 1 / 2
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨by linarith, ht.2⟩
  · rintro (ht | ht) <;> constructor <;> linarith [ht.1, ht.2]

theorem residualBridge_subset_band
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    residualBridge K e a b ⊆ residualBand K e := by
  rw [residualBridge_eq_band_radii K e heq]
  apply union_subset
  · exact ((residualBand_halfEdge_passage K e a (by simp [heq])).1.symm.subset).trans
      inter_subset_left
  · exact ((residualBand_halfEdge_passage K e b (by simp [heq])).1.symm.subset).trans
      inter_subset_left

theorem residualBridge_inter_bandRim
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    residualBridge K e a b ∩ residualBandRim K e =
      {primalEdgeMark K e a, primalEdgeMark K e b} := by
  have ha := residualBand_halfEdge_passage K e a (by simp [heq])
  have hb := residualBand_halfEdge_passage K e b (by simp [heq])
  apply Subset.antisymm
  · rintro x ⟨hx, hr⟩
    rw [residualBridge_eq_band_radii K e heq] at hx
    rcases hx with hx | hx
    · exact Or.inl (ha.2.subset ⟨hr, (ha.1.symm.subset hx).2⟩)
    · exact Or.inr (hb.2.subset ⟨hr, (hb.1.symm.subset hx).2⟩)
  · intro x hx
    rcases hx with rfl | hx
    · have ha' := primalEdgeContact_subset_bandRim K e a (by simp [heq])
        (primalEdgeMark_mem_contact K e a (by simp [heq]))
      exact ⟨left_mem_segment ℝ _ _, ha'⟩
    · have hx' : _ = primalEdgeMark K e b := hx
      rw [hx']
      have hb' := primalEdgeContact_subset_bandRim K e b (by simp [heq])
        (primalEdgeMark_mem_contact K e b (by simp [heq]))
      exact ⟨right_mem_segment ℝ _ _, hb'⟩

theorem exists_residualBand_bridge_cut
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (hab : a ≠ b) (heq : e.val = {a, b}) :
    ∃ U V d₀ d₁ : Set E,
      IsFinitePLBallPair ℝ U {primalEdgeMark K e a, primalEdgeMark K e b} ∧
      IsFinitePLBallPair ℝ V {primalEdgeMark K e a, primalEdgeMark K e b} ∧
      U ∪ V = residualBandRim K e ∧
      U ∩ V = {primalEdgeMark K e a, primalEdgeMark K e b} ∧
      IsFinitePLBallPair (ℝ × ℝ) d₀ (U ∪ residualBridge K e a b) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁ (residualBridge K e a b ∪ V) ∧
      d₀ ∪ d₁ = residualBand K e ∧ d₀ ∩ d₁ = residualBridge K e a b ∧
      d₀ ∩ residualBandRim K e = U ∧ d₁ ∩ residualBandRim K e = V := by
  have hd := residualBand_isFinitePLDisk K hpure hcofaces hlinks e
  have hW := residualBridge_isFinitePLInterval K e hab heq
  have hne := primalEdgeMark_ne K e e a b (by simp [heq]) (by simp [heq]) (Or.inr hab)
  have ha := primalEdgeContact_subset_bandRim K e a (by simp [heq])
    (primalEdgeMark_mem_contact K e a (by simp [heq]))
  have hb := primalEdgeContact_subset_bandRim K e b (by simp [heq])
    (primalEdgeMark_mem_contact K e b (by simp [heq]))
  obtain ⟨U, V, hU, hV, hUV, hinter⟩ := hd.exists_boundary_arcs ha hb hne
  have hproper : residualBridge K e a b \ {primalEdgeMark K e a, primalEdgeMark K e b} ⊆
      residualBand K e \ residualBandRim K e := by
    intro x hx
    exact ⟨residualBridge_subset_band K e heq hx.1,
      fun hr ↦ hx.2 ((residualBridge_inter_bandRim K e heq).subset ⟨hx.1, hr⟩)⟩
  obtain ⟨d₀, d₁, hd₀, hd₁, hwhole, hcommon, houter₀, houter₁⟩ :=
    hd.exists_proper_arc_cut hU hV hW hne hinter.subset hUV hproper
  exact ⟨U, V, d₀, d₁, hU, hV, hUV, hinter, hd₀, hd₁, hwhole, hcommon, houter₀, houter₁⟩

end PoincareConjecture.M76.OriginalTriangleCopies
