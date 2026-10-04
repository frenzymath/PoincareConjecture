import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.PositionedCircleGraphSurgery
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Graphs.SelectedCircleSurgeryGraph
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Graphs.SelectedCircleContactCounts

/-!
# One-sphere selection from original positioned circle surgery

The original surgery constructs both replacement spheres and their complete
finite face graph. Selecting one sphere on the original index type then
constructs its actual subgraph, strictly lowers the original graph face count,
and retains the original degree and crossing conditions. Other-face contacts
are subsets of the old contacts. This positioning result does not assert
preservation of the no-L3 complement condition.
-/

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

open scoped Classical in
/-- Select either constructed surgery sphere using the original positioning
hypotheses, retaining the original index type and a strictly smaller graph. -/
theorem exists_protected_selected_positioned_circle_surgery
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysicalGraph : Q.symm '' G.space = (⋃ i, S i) ∩
      (g '' convexHull ℝ (s : Set E)))
    (hSZ : Disjoint (⋃ i, S i) Z)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcrossings : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0)
    (hcofaces : ∀ i a, a ∈ K.faces → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅)
    (b : Bool) :
    ∃ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (n : ℕ) (L : Polygon V3 (n + 3)) (i : κ) (O C₀ : Set X) (new : Bool → Set X),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
      L.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
      IsOpen O ∧ O ⊆ Q.source ∧ Q.symm '' L.boundary ℝ ⊆ O ∧
      Disjoint O Z ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        Disjoint O (g '' convexHull ℝ (a : Set E))) ∧
      (∀ j, j ≠ i → Disjoint O (S j)) ∧
      IsCompact C₀ ∧ C₀ ⊆ O ∧
      C₀ ∩ ((⋃ j, S j) ∩ (g '' convexHull ℝ (s : Set E))) = Q.symm '' L.boundary ℝ ∧
      let S' := selectedCircleSurgeryFamily S i new b
      ∃ (H : SimplicialComplex ℝ V3) (hHG : H ≤ G.deleteEdgeComponent C),
        Nonempty (∀ j, ChartwisePLSphere e (S' j)) ∧
        (Pairwise fun j k => Disjoint (S' j) (S' k)) ∧
        Disjoint (⋃ j, S' j) Z ∧
        (∀ j a, a ∈ K.faces → a.card = 2 →
          HasOriginalEdgeCofaceCharts e (S' j) K g a) ∧
        Nat.card (Set.range S') = Nat.card κ ∧
        (⋃ j, S' j) ⊆ ⋃ j, circleSurgeryFamily S i new j ∧
        ((⋃ j, S' j) ∪ new (!b)) \ C₀ = (⋃ j, S j) \ C₀ ∧
        (⋃ j, S' j) \ C₀ ⊆ (⋃ j, S j) \ C₀ ∧
        (⋃ j, S' j) \ O ⊆ (⋃ j, S j) \ O ∧
        (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
          (⋃ j, S' j) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
            (⋃ j, S j) ∩ (g '' convexHull ℝ (a : Set E))) ∧
        (⋃ j, S' j) ∩ (g '' convexHull ℝ (s : Set E)) ⊆
          ((⋃ j, S j) ∩ (g '' convexHull ℝ (s : Set E))) \ (Q.symm '' L.boundary ℝ) ∧
        H.faces.Finite ∧ H.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
        (∀ a ∈ H.faces, a.card ≤ 2) ∧
        H.space = (G.deleteEdgeComponent C).space ∩ Q.symm ⁻¹' (⋃ j, S' j) ∧
        Q.symm '' H.space = (⋃ j, S' j) ∩ (g '' convexHull ℝ (s : Set E)) ∧
        (∀ v : H.vertices,
          (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
            ((G.deleteEdgeComponent C).vertexAbstractComplex.edgeGraph.neighborSet
              ⟨v.val, hHG v.property⟩).ncard) ∧
        (∀ v : H.vertices,
          (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
            (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
        (∀ v : H.vertices,
          (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
            (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
        (H.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
        (∀ v : H.vertices, (H.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty) ∧
        H.faces.ncard < G.faces.ncard ∧
        ∀ w ∈ H.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
          ∀ V : Set V3, IsOpen V → w ∈ V →
            ∃ B : OpenPartialHomeomorph V3 P3,
              w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
              LocallyPiecewiseAffineOn B B.source ∧
              LocallyPiecewiseAffineOn B.symm B.target ∧
              (∀ x ∈ B.source, Q.symm x ∈ ⋃ j, S' j ↔ (B x).2 = 0) ∧
              ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0 := by
  classical
  obtain ⟨C, n, L, i, O, C₀, new, hLi, hL, hLC, hLint, hO, hOQ, hrO, hOZ,
      hOfaces, hOmembers, hC₀, hC₀O, hSupportGraph, ⟨sfull⟩, hfull, hfullZ,
      hfullCofaces, _, hSupport, hExterior, hOtherFaces, hFace,
      hG', hGT', hdim', hphysical', hinterior', hexterior', hfinite', hne',
      hcount', hcrossings'⟩ :=
    exists_protected_positioned_circle_graph_surgery S sS hdis K N hK hNK g hgc hgi
      hZ hmark hs hs3 Q A hmap hA G hG hGT hphysicalGraph hSZ hdim hfinite
      hinterior hexterior he hcover hQ hcrossings hcofaces hcircle
  obtain ⟨hSselected, hselectedDis, hselectedZ, hselectedSub, hselectedCard⟩ :=
    selectedCircleSurgeryFamily_geometry S i new b sfull hfull hfullZ
  obtain ⟨H, hHG, hH, hspace, himage, _, hdegree⟩ :=
    exists_selected_circle_surgery_graph S i new b sfull hfull Q
      (G.deleteEdgeComponent C) hG' (hGT'.trans inter_subset_right) hphysical'
  have hsub : H.space ⊆ (G.deleteEdgeComponent C).space := hspace ▸ inter_subset_left
  have hselectedCofaces : ∀ j a, a ∈ K.faces → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (selectedCircleSurgeryFamily S i new b j) K g a := by
    intro j a ha ha2
    rw [selectedCircleSurgeryFamily_eq_index]
    exact hfullCofaces _ a ha ha2
  have hint (v : H.vertices)
      (hv : (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))) :
      (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 :=
    (hdegree v).trans (hinterior' ⟨v.val, hHG v.property⟩ hv)
  have hext (v : H.vertices)
      (hv : (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))) :
      (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1 :=
    (hdegree v).trans (hexterior' ⟨v.val, hHG v.property⟩ hv)
  have hselectedSupport :
      ((⋃ j, selectedCircleSurgeryFamily S i new b j) ∪ new (!b)) \ C₀ =
        (⋃ j, S j) \ C₀ := by
    rw [selectedCircleSurgeryFamily_union_omitted]
    exact hSupport
  refine ⟨C, n, L, i, O, C₀, new, hLi, hL, hLC, hLint, hO, hOQ, hrO, hOZ,
    hOfaces, hOmembers, hC₀, hC₀O, hSupportGraph, H, hHG,
    hSselected, hselectedDis, hselectedZ, hselectedCofaces, hselectedCard, hselectedSub,
    hselectedSupport, ?_, ?_, ?_, ?_, hH, hsub.trans hGT', (fun a ha => hdim' a (hHG ha)),
    hspace, himage, hdegree, hint, hext,
    hfinite'.subset (inter_subset_inter_left _ hsub), ?_,
    (G.faces_ncard_lt_of_le_deleteEdgeComponent hG C H hHG).2, ?_⟩
  · calc
      (⋃ j, selectedCircleSurgeryFamily S i new b j) \ C₀ ⊆
          ((⋃ j, selectedCircleSurgeryFamily S i new b j) ∪ new (!b)) \ C₀ :=
        sdiff_subset_sdiff_left subset_union_left
      _ = (⋃ j, S j) \ C₀ := hselectedSupport
  · exact (sdiff_subset_sdiff_left hselectedSub).trans hExterior.subset
  · intro a ha hac hane
    exact selectedCircleSurgeryFamily_inter_subset_of_full S i new b
      (hOtherFaces a ha hac hane).subset
  · exact (inter_subset_inter_left _ hselectedSub).trans hFace.subset
  · intro v
    by_cases hv : (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))
    · exact nonempty_of_ncard_ne_zero (by rw [hint v hv]; decide)
    · exact nonempty_of_ncard_ne_zero (by rw [hext v hv]; decide)
  · intro w hw
    have hwH := hw.1
    rw [hspace] at hwH
    exact selected_circle_surgery_paired_crossings S i new b sfull hfull Q
      (hGT' hwH.1).2 hwH.2 (hcrossings' w ⟨hwH.1, hw.2⟩)

end PoincareMT.M76
