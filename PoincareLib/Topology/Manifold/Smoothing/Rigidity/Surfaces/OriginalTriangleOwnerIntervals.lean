import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTriangleCopiedEdges
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusLeafCutDisk
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.DualFaceGraph

/-!
# Dual-tree owners for copied boundary intervals

Every edge of the complementary dual graph retains its two original
triangle cofaces.  This file exposes one of those cofaces as an actual
owner of the separated copied interval, including its exact sheet and
endpoint contacts.  The result is the local input needed before attaching
the interval to the global leaf-cut rim.
-/

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareMT.M76.OriginalTriangleCopies

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- A complementary dual edge has an actual triangle coface that contains
the exact original edge label. -/
theorem exists_complementary_triangle_owner
    {V : Type*} [Fintype V] {A : AbstractSimplicialComplex V} (T : SimpleGraph V)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (s : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex T).edgeSet) :
    ∃ q : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      A.toPreAbstractSimplicialComplex,
      q ∈ s.val ∧
        (complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex T
          hcofaces s).val.val ⊆ q.val := by
  rcases s with ⟨s, hs⟩
  induction s using Sym2.ind with
  | h q r =>
    refine ⟨q, Sym2.mem_mk_left q r, ?_⟩
    exact complementaryTriangleEdgeEquiv_subset
      A.toPreAbstractSimplicialComplex T hcofaces
      ⟨Sym2.mk q r, hs⟩ q (Sym2.mem_mk_left q r)

theorem complementary_owner_edge_subset
    {V : Type*} [Fintype V] {A : AbstractSimplicialComplex V} (T : SimpleGraph V)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (s : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex T).edgeSet) :
    ∃ q : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      A.toPreAbstractSimplicialComplex,
      q ∈ s.val ∧
        (complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex T
          hcofaces s).val.val ⊆ q.val :=
  exists_complementary_triangle_owner T hcofaces s

/- The complementary edge retains both of its distinct triangle cofaces.  The
two witnesses are kept explicit because the two Boolean boundary copies live
in different separated sheets. -/
theorem exists_complementary_triangle_owner_pair
    {V : Type*} [Fintype V] {A : AbstractSimplicialComplex V} (T : SimpleGraph V)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (s : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex T).edgeSet) :
    ∃ q r : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      A.toPreAbstractSimplicialComplex,
      q ∈ s.val ∧ r ∈ s.val ∧ q ≠ r ∧
        (complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex T
          hcofaces s).val.val ⊆ q.val ∧
        (complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex T
          hcofaces s).val.val ⊆ r.val := by
  rcases s with ⟨s, hs⟩
  induction s using Sym2.ind with
  | h q r =>
    have hqr :=
      ((complementaryTriangleGraph A.toPreAbstractSimplicialComplex T).mem_edgeSet.mp hs).1
    refine ⟨q, r, Sym2.mem_mk_left q r, Sym2.mem_mk_right q r, hqr, ?_, ?_⟩
    · exact complementaryTriangleEdgeEquiv_subset
        A.toPreAbstractSimplicialComplex T hcofaces ⟨Sym2.mk q r, hs⟩ q
          (Sym2.mem_mk_left q r)
    · exact complementaryTriangleEdgeEquiv_subset
        A.toPreAbstractSimplicialComplex T hcofaces ⟨Sym2.mk q r, hs⟩ r
          (Sym2.mem_mk_right q r)

theorem selected_triangle_owner_mem
    {A : AbstractSimplicialComplex E}
    {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      A.toPreAbstractSimplicialComplex)}
    (p : D.incidenceSubdivision ↪g
      (A.toPreAbstractSimplicialComplex).faceInclusionGraph)
    {S : Set A.toPreAbstractSimplicialComplex.faces}
    (hS : S = Set.range p)
    (q : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      A.toPreAbstractSimplicialComplex) :
    p (Sum.inl q) ∈ S := by
  rw [hS]
  exact ⟨Sum.inl q, rfl⟩

theorem complementary_edge_vertex_not_selected
    {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (r : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
    {S : Set K.barycentricSubdivision.vertices}
    (hS : S = Set.range
      ((PoincareMT.M76.dualIncidenceRestriction K.vertexAbstractComplex P D hD).trans r))
    (s : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet) :
    r (Sum.inr s) ∉ S := by
  rw [hS]
  rintro ⟨x, hx⟩
  have hEq := r.injective hx.symm
  rcases x with x | x
  · cases hEq
  · change Sum.inr s = Sum.inr
      (⟨x.val, SimpleGraph.edgeSet_mono hD x.property⟩ :
        (complementaryTriangleGraph
          K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet) at hEq
    have hsub : s = ⟨x.val, SimpleGraph.edgeSet_mono hD x.property⟩ :=
      Sum.inr.inj hEq
    apply hs
    rw [congrArg Subtype.val hsub]
    exact x.property

/- The selected triangle endpoint and the unselected complementary-edge
vertex determine an actual dual block on the copied-disk rim.  This is kept
as a separate producer from the interval theorem so downstream side assembly
can transport the same block through its chosen owner. -/
theorem complementary_edge_owner_selected_unselected
    {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (r : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
    {S : Set K.barycentricSubdivision.vertices}
    (hS : S = Set.range
      ((PoincareMT.M76.dualIncidenceRestriction K.vertexAbstractComplex P D hD).trans r))
    (s : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet) :
    ∃ q : PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      q ∈ s.val ∧
        (complementaryTriangleEdgeEquiv K.vertexAbstractComplex.toPreAbstractSimplicialComplex
          P (by
            intro e
            rw [K.triangleCofaces_card_eq_original e]
            apply hcofaces _ e.property.1
            simpa only [Finset.card_map] using e.property.2) s).val.val ⊆ q.val ∧
        r (Sum.inl q) ∈ S ∧ r (Sum.inr s) ∉ S := by
  let A := K.vertexAbstractComplex
  let hcounts (e : Edge A.toPreAbstractSimplicialComplex) :
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original e]
    apply hcofaces _ e.property.1
    simpa only [Finset.card_map] using e.property.2
  obtain ⟨q, hq, hsub⟩ := exists_complementary_triangle_owner P hcounts s
  have hqS : r (Sum.inl q) ∈ S := by
    rw [hS]
    exact ⟨Sum.inl q, rfl⟩
  have hsS : r (Sum.inr s) ∉ S :=
    complementary_edge_vertex_not_selected P D hD r hS s hs
  exact ⟨q, hq, hsub, hqS, hsS⟩

/- The geometric version is stated for an arbitrary owner witness.  Keeping
the witness explicit avoids choosing a noncanonical coface in the copied
carrier and lets the later rim assembly transport it through its own map. -/
theorem copied_owner_interval_subset
    (K : SimplicialComplex ℝ E)
    (label : Triangle K → ℝ) (s : Triangle K)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ambientEdge K e ⊆ s.val) :
    Set.range (copiedEdgePath K label s e he) ⊆ copy K label s := by
  rw [copiedEdgePath_image K label s e he]
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, convexHull_mono (Finset.coe_subset.mpr he) hx, rfl⟩

theorem copied_owner_interval_zero
    (K : SimplicialComplex ℝ E)
    (label : Triangle K → ℝ) (s : Triangle K)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ambientEdge K e ⊆ s.val) :
    copiedEdgePath K label s e he 0 =
      inclusion (E := E) (label s)
        (PoincareMT.M76.residualEdgeEndpoints K e).1 := by
  simp [copiedEdgePath, inclusion, ContinuousAffineMap.coe_lineMap_eq,
    AffineMap.lineMap_apply_zero]

theorem copied_owner_interval_one
    (K : SimplicialComplex ℝ E)
    (label : Triangle K → ℝ) (s : Triangle K)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ambientEdge K e ⊆ s.val) :
    copiedEdgePath K label s e he 1 =
      inclusion (E := E) (label s)
        (PoincareMT.M76.residualEdgeEndpoints K e).2 := by
  simp [copiedEdgePath, inclusion, ContinuousAffineMap.coe_lineMap_eq,
    AffineMap.lineMap_apply_one]

theorem complementary_edge_owner_copied_data
    {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (r : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
    {S : Set K.barycentricSubdivision.vertices}
    (hS : S = Set.range
      ((PoincareMT.M76.dualIncidenceRestriction K.vertexAbstractComplex P D hD).trans r))
    (s : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet)
    (label : Triangle K → ℝ) :
    ∃ (q : Triangle K)
      (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
      (he : ambientEdge K e ⊆ q.val),
      Set.range (copiedEdgePath K label q e he) ⊆ copy K label q ∧
      copiedEdgePath K label q e he 0 =
        inclusion (E := E) (label q)
          (PoincareMT.M76.residualEdgeEndpoints K e).1 ∧
      copiedEdgePath K label q e he 1 =
        inclusion (E := E) (label q)
          (PoincareMT.M76.residualEdgeEndpoints K e).2 := by
  obtain ⟨q, hq, hsub, _, _⟩ :=
    complementary_edge_owner_selected_unselected hcofaces P D hD r hS s hs
  let hcounts (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
      (triangleCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original e]
    apply hcofaces _ e.property.1
    simpa only [Finset.card_map] using e.property.2
  let e := complementaryTriangleEdgeEquiv
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex P hcounts s
  let emb : K.vertices ↪ E := Function.Embedding.subtype _
  let qK : Triangle K :=
    ⟨q.val.map emb, by
      change q.val.map emb ∈ K.faces
      exact q.property.1, by
      simpa only [Finset.card_map] using q.property.2⟩
  have he : ambientEdge K e ⊆ qK.val := by
    simpa only [ambientEdge, qK, emb] using (Finset.map_subset_map.mpr hsub)
  exact ⟨qK, e, he,
    copied_owner_interval_subset K label qK e he,
    copied_owner_interval_zero K label qK e he,
    copied_owner_interval_one K label qK e he⟩

/- The actual four-side local package: one residual edge contributes the two
separated coface intervals, and the Boolean coordinate selects the sheet. -/
theorem complementary_edge_owner_copied_pair_data
    {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (r : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
    {S : Set K.barycentricSubdivision.vertices}
    (hS : S = Set.range
      ((PoincareMT.M76.dualIncidenceRestriction K.vertexAbstractComplex P D hD).trans r))
    (s : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet)
    (label : Triangle K → ℝ) :
    ∃ (q₀ q₁ : Triangle K)
      (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
      (he₀ : ambientEdge K e ⊆ q₀.val)
      (he₁ : ambientEdge K e ⊆ q₁.val),
      q₀ ≠ q₁ ∧
      r (Sum.inr s) ∉ S ∧
      (Set.range (copiedEdgePath K label q₀ e he₀) ⊆ copy K label q₀) ∧
      (Set.range (copiedEdgePath K label q₁ e he₁) ⊆ copy K label q₁) ∧
      IsFinitePLBallPair ℝ (Set.range (copiedEdgePath K label q₀ e he₀))
        ({inclusion (E := E) (label q₀)
            (PoincareMT.M76.residualEdgeEndpoints K e).1,
          inclusion (E := E) (label q₀)
            (PoincareMT.M76.residualEdgeEndpoints K e).2} : Set (E × ℝ)) ∧
      IsFinitePLBallPair ℝ (Set.range (copiedEdgePath K label q₁ e he₁))
        ({inclusion (E := E) (label q₁)
            (PoincareMT.M76.residualEdgeEndpoints K e).1,
          inclusion (E := E) (label q₁)
            (PoincareMT.M76.residualEdgeEndpoints K e).2} : Set (E × ℝ)) ∧
      copiedEdgePath K label q₀ e he₀ 0 =
        inclusion (E := E) (label q₀)
          (PoincareMT.M76.residualEdgeEndpoints K e).1 ∧
      copiedEdgePath K label q₀ e he₀ 1 =
        inclusion (E := E) (label q₀)
          (PoincareMT.M76.residualEdgeEndpoints K e).2 ∧
      copiedEdgePath K label q₁ e he₁ 0 =
        inclusion (E := E) (label q₁)
          (PoincareMT.M76.residualEdgeEndpoints K e).1 ∧
      copiedEdgePath K label q₁ e he₁ 1 =
        inclusion (E := E) (label q₁)
          (PoincareMT.M76.residualEdgeEndpoints K e).2 := by
  obtain ⟨q, q', hq, hq', hqq', hsub, hsub'⟩ :=
    exists_complementary_triangle_owner_pair P (by
      intro e
      rw [K.triangleCofaces_card_eq_original e]
      apply hcofaces _ e.property.1
      simpa only [Finset.card_map] using e.property.2) s
  have hsS : r (Sum.inr s) ∉ S :=
    complementary_edge_vertex_not_selected P D hD r hS s hs
  let hcounts (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
      (triangleCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original e]
    apply hcofaces _ e.property.1
    simpa only [Finset.card_map] using e.property.2
  let e := complementaryTriangleEdgeEquiv
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex P hcounts s
  let emb : K.vertices ↪ E := Function.Embedding.subtype _
  let qK : Triangle K :=
    ⟨q.val.map emb, by
      change q.val.map emb ∈ K.faces
      exact q.property.1, by
      simpa only [Finset.card_map] using q.property.2⟩
  let qK' : Triangle K :=
    ⟨q'.val.map emb, by
      change q'.val.map emb ∈ K.faces
      exact q'.property.1, by
      simpa only [Finset.card_map] using q'.property.2⟩
  have he₀ : ambientEdge K e ⊆ qK.val := by
    simpa only [ambientEdge, qK, emb] using (Finset.map_subset_map.mpr hsub)
  have he₁ : ambientEdge K e ⊆ qK'.val := by
    simpa only [ambientEdge, qK', emb] using (Finset.map_subset_map.mpr hsub')
  have hne : qK ≠ qK' := by
    intro h
    apply hqq'
    apply Subtype.ext
    have hm : qK.val = qK'.val := congrArg Subtype.val h
    change q.val.map emb = q'.val.map emb at hm
    exact Finset.map_injective emb hm
  refine ⟨qK, qK', e, he₀, he₁, hne, hsS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact copied_owner_interval_subset K label qK e he₀
  · exact copied_owner_interval_subset K label qK' e he₁
  · exact copiedEdgePath_isFinitePLBallPair K label qK e he₀
  · exact copiedEdgePath_isFinitePLBallPair K label qK' e he₁
  · exact copied_owner_interval_zero K label qK e he₀
  · exact copied_owner_interval_one K label qK e he₀
  · exact copied_owner_interval_zero K label qK' e he₁
  · exact copied_owner_interval_one K label qK' e he₁

end PoincareMT.M76.OriginalTriangleCopies
