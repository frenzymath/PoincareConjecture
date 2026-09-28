import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalTreeNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.RetainedEdgeFibers
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.DualEdgePassage









set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

omit [FiniteDimensional ℝ E] in
theorem originalVertexCentroid_val (v : K.vertices) :
    (originalVertexCentroid K v).val = v.val := by
  change (({v} : Finset K.vertices).map (Function.Embedding.subtype _)).centroid ℝ id = v.val
  simp only [Finset.map_singleton, Function.Embedding.coe_subtype,
    Finset.centroid_singleton, id_eq]

omit [FiniteDimensional ℝ E] in
theorem originalEdgeCentroid_val
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    (originalEdgeCentroid K e).val = AffineMap.lineMap a.val b.val (1 / 2 : ℝ) := by
  change (e.val.map (Function.Embedding.subtype _)).centroid ℝ id = _
  rw [heq]
  simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype,
    Finset.centroid_pair, id_eq, vsub_eq_sub, vadd_eq_add, AffineMap.lineMap_apply]
  module

omit [FiniteDimensional ℝ E] in
theorem primalEdgeMark_first_formula
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    primalEdgeMark K e a = AffineMap.lineMap a.val b.val (1 / 4 : ℝ) := by
  rw [primalEdgeMark, originalVertexCentroid_val, originalEdgeCentroid_val K e heq]
  simp only [Finset.centroid_pair, id_eq, vsub_eq_sub, vadd_eq_add, AffineMap.lineMap_apply]
  module

omit [FiniteDimensional ℝ E] in
theorem primalEdgeMark_second_formula
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    primalEdgeMark K e b = AffineMap.lineMap a.val b.val (3 / 4 : ℝ) := by
  rw [primalEdgeMark, originalVertexCentroid_val, originalEdgeCentroid_val K e heq]
  simp only [Finset.centroid_pair, id_eq, vsub_eq_sub, vadd_eq_add, AffineMap.lineMap_apply]
  module

omit [FiniteDimensional ℝ E] [DecidableEq E] in
private theorem segment_lineMap_image (a b : E) {u v : ℝ} (huv : u ≤ v) :
    segment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) =
      AffineMap.lineMap a b '' Icc u v := by
  rw [← image_segment ℝ (AffineMap.lineMap a b), segment_eq_Icc huv]

noncomputable def residualBridge
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (a b : K.vertices) : Set E :=
  segment ℝ (primalEdgeMark K e a) (primalEdgeMark K e b)

omit [FiniteDimensional ℝ E] in
theorem residualBridge_eq_image
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    residualBridge K e a b = AffineMap.lineMap a.val b.val '' Icc (1 / 4 : ℝ) (3 / 4) := by
  rw [residualBridge, primalEdgeMark_first_formula K e heq,
    primalEdgeMark_second_formula K e heq, segment_lineMap_image _ _ (by norm_num)]

theorem residualBridge_subset_openEdge
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (heq : e.val = {a, b}) :
    residualBridge K e a b ⊆ openSegment ℝ a.val b.val := by
  rw [residualBridge_eq_image K e heq, openSegment_eq_image_lineMap]
  apply image_mono
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem primal_halfEdge_passage [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ¬ edgeInGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P e)
    (v : K.vertices) (hv : v ∈ e.val) :
    K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ∩
        segment ℝ v.val (originalEdgeCentroid K e).val =
      segment ℝ v.val (primalEdgeMark K e v) := by
  have hadj := originalVertexCentroid_adj_edgeCentroid K e v hv
  have hface : ({(originalVertexCentroid K v).val, (originalEdgeCentroid K e).val} :
      Finset E) ∈ K.barycentricSubdivision.faces := by
    have hf := hadj.2
    change (({originalVertexCentroid K v, originalEdgeCentroid K e} :
      Finset K.barycentricSubdivision.vertices).map (Function.Embedding.subtype _)) ∈
      K.barycentricSubdivision.faces at hf
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hf
  have h := (K.barycentricSubdivision.vertexDualUnion_edge_passage
    (primalCentroidSet K P hP) (originalVertexCentroid K v) (originalEdgeCentroid K e)
    hadj.ne hface (originalVertexCentroid_mem_primalCentroidSet K P hP v)
    (originalEdgeCentroid_not_mem_primalCentroidSet K P hP e he)).2.1
  simpa only [primalEdgeMark, originalVertexCentroid_val] using h

theorem residualBridge_inter_primal [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices) (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ¬ edgeInGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P e)
    {a b : K.vertices} (hab : a ≠ b) (heq : e.val = {a, b}) :
    K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ∩
        residualBridge K e a b = {primalEdgeMark K e a, primalEdgeMark K e b} := by
  let l := AffineMap.lineMap (k := ℝ) a.val b.val
  have hlinj : Function.Injective l :=
    AffineMap.lineMap_injective ℝ (fun h ↦ hab (Subtype.ext h))
  have ha := primal_halfEdge_passage K P hP e he a (by simp [heq])
  have hb := primal_halfEdge_passage K P hP e he b (by simp [heq])
  rw [originalEdgeCentroid_val K e heq, primalEdgeMark_first_formula K e heq] at ha
  rw [originalEdgeCentroid_val K e heq, primalEdgeMark_second_formula K e heq] at hb
  have ha' : K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ∩
      l '' Icc (0 : ℝ) (1 / 2) = l '' Icc (0 : ℝ) (1 / 4) := by
    rw [← segment_lineMap_image _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← segment_lineMap_image _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    simpa only [AffineMap.lineMap_apply_zero] using ha
  have hb' : K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ∩
      l '' Icc (1 / 2 : ℝ) 1 = l '' Icc (3 / 4 : ℝ) 1 := by
    rw [segment_symm ℝ b.val, segment_symm ℝ b.val] at hb
    rw [← segment_lineMap_image _ _ (by norm_num : (1 / 2 : ℝ) ≤ 1),
      ← segment_lineMap_image _ _ (by norm_num : (3 / 4 : ℝ) ≤ 1)]
    simpa only [AffineMap.lineMap_apply_one] using hb
  rw [residualBridge_eq_image K e heq, primalEdgeMark_first_formula K e heq,
    primalEdgeMark_second_formula K e heq]
  ext x
  constructor
  · rintro ⟨hx, t, ht, rfl⟩
    by_cases hhalf : t ≤ 1 / 2
    · obtain ⟨u, hu, hut⟩ := ha'.subset ⟨hx, t, ⟨by linarith [ht.1], hhalf⟩, rfl⟩
      have hut' : u = t := hlinj hut
      have ht' : t = 1 / 4 := by linarith [hu.2, ht.1]
      simp [ht']
    · obtain ⟨u, hu, hut⟩ := hb'.subset ⟨hx, t, ⟨by linarith, by linarith [ht.2]⟩, rfl⟩
      have hut' : u = t := hlinj hut
      have ht' : t = 3 / 4 := by linarith [hu.1, ht.2]
      simp [ht']
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨(ha'.symm.subset ⟨1 / 4, by norm_num, rfl⟩).1,
        1 / 4, by norm_num, rfl⟩
    · have hx' : x = l (3 / 4) := hx
      subst x
      exact ⟨(hb'.symm.subset ⟨3 / 4, by norm_num, rfl⟩).1,
        3 / 4, by norm_num, rfl⟩

theorem residualBridge_disjoint
    (e f : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (hef : e ≠ f) {a b c d : K.vertices} (hab : a ≠ b)
    (heq : e.val = {a, b}) (hfq : f.val = {c, d}) :
    Disjoint (residualBridge K e a b) (residualBridge K f c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hxe := residualBridge_subset_openEdge K e heq hx
  have hxf := openSegment_subset_segment ℝ c.val d.val
    (residualBridge_subset_openEdge K f hfq hy)
  have heface : ({a.val, b.val} : Finset E) ∈ K.faces := by
    have hh := e.property.1
    change e.val.map (Function.Embedding.subtype _) ∈ K.faces at hh
    simpa only [heq, Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] using hh
  have hfface : ({c.val, d.val} : Finset E) ∈ K.faces := by
    have hh := f.property.1
    change f.val.map (Function.Embedding.subtype _) ∈ K.faces at hh
    simpa only [hfq, Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] using hh
  have hsub := edge_subset_of_mem_openSegment_mem_convexHull K
    (fun h ↦ hab (Subtype.ext h)) heface hxe hfface
    (by simpa only [Finset.coe_pair, convexHull_pair] using hxf)
  have hsub' : e.val ⊆ f.val := by
    rw [heq, hfq]
    intro v hv
    have hh : v.val ∈ ({a.val, b.val} : Finset E) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, Subtype.val_inj] using hv
    have hh' := hsub hh
    simpa only [Finset.mem_insert, Finset.mem_singleton, Subtype.val_inj] using hh'
  apply hef
  exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub'
    (by rw [e.property.2, f.property.2]))

theorem residualBridge_isFinitePLInterval [Fintype K.barycentricSubdivision.faces]
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (hab : a ≠ b) (heq : e.val = {a, b}) :
    IsFinitePLBallPair ℝ (residualBridge K e a b)
      {primalEdgeMark K e a, primalEdgeMark K e b} := by
  let A := ContinuousAffineMap.lineMap (R := ℝ) (primalEdgeMark K e a) (primalEdgeMark K e b)
  have hne := primalEdgeMark_ne K e e a b (by simp [heq]) (by simp [heq]) (Or.inr hab)
  have hinj : InjOn A (Icc (0 : ℝ) 1) := (AffineMap.lineMap_injective ℝ hne).injOn
  have h := isFinitePLBallPair_affine_interval (show (0 : ℝ) < 1 by norm_num) A hinj
  simpa only [A, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap, residualBridge] using h


theorem residualBridge_lineMap_spec [Fintype K.barycentricSubdivision.faces]
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (hab : a ≠ b) (heq : e.val = {a, b}) :
    let A := ContinuousAffineMap.lineMap (R := ℝ)
      (primalEdgeMark K e a) (primalEdgeMark K e b)
    FinitePiecewiseAffineOn A (Icc (0 : ℝ) 1) ∧ Function.Injective A ∧
      A '' Icc (0 : ℝ) 1 = residualBridge K e a b ∧
      A 0 = primalEdgeMark K e a ∧ A 1 = primalEdgeMark K e b := by
  intro A
  have hPL : FinitePiecewiseAffineOn A (Icc (0 : ℝ) 1) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
    exact ⟨J, hJ, hJs, J.affineOnFaces_affine A⟩
  have hne := primalEdgeMark_ne K e e a b (by simp [heq]) (by simp [heq]) (Or.inr hab)
  refine ⟨hPL, AffineMap.lineMap_injective ℝ hne, ?_, ?_, ?_⟩
  · exact (segment_eq_image_lineMap ℝ _ _).symm
  · exact AffineMap.lineMap_apply_zero _ _
  · exact AffineMap.lineMap_apply_one _ _

end PoincareConjecture.M76.OriginalTriangleCopies
