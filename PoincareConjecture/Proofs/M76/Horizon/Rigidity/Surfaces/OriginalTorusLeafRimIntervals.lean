import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusLeafCutDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTriangleOwnerIntervals
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SurfaceDualEdgeGeometry

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem selected_unselected_dual_interval_on_leaf_rim
    {K : SimplicialComplex ℝ E} [Fintype K.faces]
    {S : Set K.vertices} {p q : K.vertices}
    (hp : p ∈ S) (hq : q ∈ Sᶜ) (hpq : p.val ≠ q.val)
    (he : ({p.val, q.val} : Finset E) ∈ K.faces)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) :
    ∃ t ∈ K.faces, ∃ u ∈ K.faces,
      t.card = 3 ∧ u.card = 3 ∧
      ({p.val, q.val} : Finset E) ⊆ t ∧
      ({p.val, q.val} : Finset E) ⊆ u ∧
      t.centroid ℝ id ≠ u.centroid ℝ id ∧
      IsFinitePLBallPair ℝ (K.barycentricDualBlock {p.val, q.val}).space
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      ({p.val, q.val} : Finset E).centroid ℝ id ∈
        (K.barycentricDualBlock {p.val, q.val}).space \
          {t.centroid ℝ id, u.centroid ℝ id} ∧
      (K.barycentricDualBlock {p.val, q.val}).space ∩
          (⋃ z ∈ K.vertices \ {p.val, q.val},
            (K.barycentricDualBlock {z}).space) =
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      (K.barycentricDualBlock {p.val, q.val}).space ⊆ K.vertexDualRim S := by
  classical
  obtain ⟨t, ht, u, hu, htc, huc, hpt, hpu, hcent, hpair, hfacet, hcontact⟩ :=
    K.exists_surface_dual_edge_interval hbound hcofaces hpq he
  have hrim := vertexDualRim_contains_selected_unselected_block
    (K := K) hp hq
  have hrim' :
      (K.barycentricDualBlock ({p.val, q.val} : Finset E)).space ⊆
        K.vertexDualRim S := by
    convert hrim using 1
    apply congrArg (fun z : Finset E => (K.barycentricDualBlock z).space)
    ext x
    simp
  exact ⟨t, ht, u, hu, htc, huc, hpt, hpu, hcent, hpair, hfacet, hcontact, hrim'⟩

open PreAbstractSimplicialComplex.ModTwoCochains

theorem residual_owner_interval_on_leaf_rim
    {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (r : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
    {S : Set K.barycentricSubdivision.vertices}
    (hS : S = Set.range ((dualIncidenceRestriction K.vertexAbstractComplex P D hD).trans r))
    (s : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet)
    (q : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex) (hq : q ∈ s.val) :
    let J := K.barycentricSubdivision
    let a := (r (Sum.inl q)).val
    let b := (r (Sum.inr s)).val
    ∃ t ∈ J.faces, ∃ u ∈ J.faces,
      t.card = 3 ∧ u.card = 3 ∧
      ({a, b} : Finset E) ⊆ t ∧ ({a, b} : Finset E) ⊆ u ∧
      t.centroid ℝ id ≠ u.centroid ℝ id ∧
      IsFinitePLBallPair ℝ (J.barycentricDualBlock {a, b}).space
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      ({a, b} : Finset E).centroid ℝ id ∈ (J.barycentricDualBlock {a, b}).space \
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      (J.barycentricDualBlock {a, b}).space ∩
        (⋃ z ∈ J.vertices \ {a, b}, (J.barycentricDualBlock {z}).space) =
          {t.centroid ℝ id, u.centroid ℝ id} ∧
      (J.barycentricDualBlock {a, b}).space ⊆ J.vertexDualRim S := by
  classical
  have hbound : ∀ t ∈ K.faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, huc, htu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  have hbound' : ∀ t ∈ K.barycentricSubdivision.faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, huc, htu⟩ := K.barycentricSubdivision_pure_triangles hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  have hselected : r (Sum.inl q) ∈ S := by
    rw [hS]
    exact ⟨Sum.inl q, rfl⟩
  have hunselected : r (Sum.inr s) ∈ Sᶜ :=
    OriginalTriangleCopies.complementary_edge_vertex_not_selected P D hD r hS s hs
  have hadj : K.barycentricSubdivision.vertexAbstractComplex.edgeGraph.Adj
      (r (Sum.inl q)) (r (Sum.inr s)) := r.map_rel_iff.mpr hq
  have hne : (r (Sum.inl q)).val ≠ (r (Sum.inr s)).val :=
    fun h => hadj.1 (Subtype.ext h)
  have hface : ({(r (Sum.inl q)).val, (r (Sum.inr s)).val} : Finset E) ∈
      K.barycentricSubdivision.faces := by
    have h := hadj.2
    change ({r (Sum.inl q), r (Sum.inr s)} : Finset K.barycentricSubdivision.vertices).map
      (Function.Embedding.subtype _) ∈ K.barycentricSubdivision.faces at h
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using h
  exact selected_unselected_dual_interval_on_leaf_rim hselected hunselected hne hface
    hbound' (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces)

end PoincareConjecture.M76.PeriodicSquare
