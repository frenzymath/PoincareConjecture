import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.PositionedCircleCofaceSurgery
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.CircleSurgeryCrossings
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Graphs.CircleSurgeryGraph

/-!
# Protected circle surgery with its literal replacement graph

The source surgery constructs the two replacement spheres and compact support.
The new finite family retains all other original members. Its selected-face
graph is the original component deletion, and every surviving paired crossing
chart is restricted away from the same compact support.
-/

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem exists_protected_positioned_circle_graph_surgery
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
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) :
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
      let S' := circleSurgeryFamily S i new
      let G' := G.deleteEdgeComponent C
      Nonempty (∀ j, ChartwisePLSphere e (S' j)) ∧
      (Pairwise fun j k => Disjoint (S' j) (S' k)) ∧
      Disjoint (⋃ j, S' j) Z ∧
      (∀ j a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S' j) K g a) ∧
      Nat.card ({j : κ // j ≠ i} ⊕ Bool) = Nat.card κ + 1 ∧
      (⋃ j, S' j) \ C₀ = (⋃ j, S j) \ C₀ ∧
      (⋃ j, S' j) \ O = (⋃ j, S j) \ O ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        (⋃ j, S' j) ∩ (g '' convexHull ℝ (a : Set E)) =
          (⋃ j, S j) ∩ (g '' convexHull ℝ (a : Set E))) ∧
      (⋃ j, S' j) ∩ (g '' convexHull ℝ (s : Set E)) =
        ((⋃ j, S j) ∩ (g '' convexHull ℝ (s : Set E))) \ (Q.symm '' L.boundary ℝ) ∧
      G'.faces.Finite ∧ G'.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
      (∀ a ∈ G'.faces, a.card ≤ 2) ∧
      Q.symm '' G'.space = (⋃ j, S' j) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ v : G'.vertices, (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G'.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      (∀ v : G'.vertices, (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G'.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
      (G'.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      (∀ v : G'.vertices, (G'.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty) ∧
      G'.faces.ncard < G.faces.ncard ∧
      ∀ w ∈ G'.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ V : Set V3, IsOpen V → w ∈ V →
          ∃ B : OpenPartialHomeomorph V3 P3,
            w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, Q.symm x ∈ ⋃ j, S' j ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0 := by
  obtain ⟨C, n, L, i, O, new, hLi, hL, hLC, hLint, hO, hOQ, hrO, hOZ,
      hOfaces, hOmembers, hnewSphere, hnewDis, hnewOther, hnewZ, hExterior, hOtherFaces,
      hFace, hCompactSupport, hnewCofaces⟩ :=
    exists_protected_positioned_circle_coface_surgery S sS hdis K N hK hNK g hgc hgi
      hZ hmark hs hs3 Q A hmap hA G hG hGT hphysicalGraph hSZ hdim hfinite
      hinterior hexterior he hcover hQ hcrossings hcofaces hcircle
  obtain ⟨C₀, hC₀, hC₀O, hSupport, hSupportGraph⟩ := hCompactSupport
  obtain ⟨snew⟩ := hnewSphere
  have hCO : Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ O :=
    hLC ▸ hrO
  have hFace' : (new true ∪ new false) ∩ (g '' convexHull ℝ (s : Set E)) =
      (S i ∩ (g '' convexHull ℝ (s : Set E))) \
        (Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))) :=
    hLC ▸ hFace
  obtain ⟨hG', hGT', hdim', hphysical', hinterior', hexterior', hfinite', hne', hcount⟩ :=
    circleSurgeryFamily_graph S i new Q G C hG hGT hphysicalGraph hdim hinterior hexterior
      hfinite hCO hOmembers hFace'
  have hFamilySupport := circleSurgeryFamily_sdiff S i new hSupport
  have hFamilyFace := circleSurgeryFamily_inter S i new hrO hOmembers hFace
  have hFamilyCofaces : ∀ j a, a ∈ K.faces → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (circleSurgeryFamily S i new j) K g a := by
    intro j a ha ha2
    cases j with
    | inl j => exact hcofaces j.val a ha ha2
    | inr b => exact hnewCofaces b a ha ha2
  refine ⟨C, n, L, i, O, C₀, new, hLi, hL, hLC, hLint, hO, hOQ, hrO, hOZ,
    hOfaces, hOmembers, hC₀, hC₀O, hSupportGraph,
    circleSurgeryFamily_spheres S i new sS snew,
    circleSurgeryFamily_pairwise_disjoint S i new hdis hnewDis hnewOther,
    circleSurgeryFamily_disjoint_marked S i new hSZ hnewZ, hFamilyCofaces,
    circleSurgeryFamily_index_card i, hFamilySupport,
    circleSurgeryFamily_sdiff S i new hExterior,
    (fun a ha hac hane => circleSurgeryFamily_inter_eq S i new (hOtherFaces a ha hac hane)),
    hFamilyFace, hG', hGT', hdim', hphysical', hinterior', hexterior', hfinite', hne',
    hcount, ?_⟩
  intro w hw
  have hwQ : w ∈ Q.target := (hGT' hw.1).2
  have hwNew : Q.symm w ∈ (⋃ j, circleSurgeryFamily S i new j) ∩
      (g '' convexHull ℝ (s : Set E)) := hphysical'.subset ⟨w, hw.1, rfl⟩
  have hwOld := hFamilyFace.subset hwNew
  have hwC₀ : Q.symm w ∉ C₀ := by
    intro hwC
    exact hwOld.2 (hSupportGraph.subset ⟨hwC, hwOld.1⟩)
  have hwG : w ∈ G.space := by
    obtain ⟨z, hz, hzw⟩ := hphysicalGraph.symm.subset hwOld.1
    exact (Q.symm.injOn (hGT hz).2 hwQ hzw) ▸ hz
  exact paired_face_crossings_of_equal_off_closed Q hC₀.isClosed hFamilySupport hwQ hwC₀
    (hcrossings w ⟨hwG, hw.2⟩)

end PoincareMT.M76
