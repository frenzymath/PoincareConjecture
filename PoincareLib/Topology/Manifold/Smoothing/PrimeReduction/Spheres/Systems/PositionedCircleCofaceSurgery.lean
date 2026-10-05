import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.PositionedCircleSurgery
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.CircleSurgeryCofaceTransport

/-!
# Protected circle surgery retaining every original edge coface chart

The constructed compact surgery support lies in the protected face
neighborhood. Every original edge is a different face from the selected
triangle, so the support misses its entire carrier. The original coface
charts consequently restrict to each of the two new sphere germs.
-/

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareMT.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

theorem exists_protected_positioned_circle_coface_surgery
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
      (n : ℕ) (L : Polygon V3 (n + 3)) (i : κ) (O : Set X) (new : Bool → Set X),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
      L.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
      IsOpen O ∧ O ⊆ Q.source ∧ Q.symm '' L.boundary ℝ ⊆ O ∧
      Disjoint O Z ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        Disjoint O (g '' convexHull ℝ (a : Set E))) ∧
      (∀ j, j ≠ i → Disjoint O (S j)) ∧
      Nonempty (∀ b, ChartwisePLSphere e (new b)) ∧
      Disjoint (new true) (new false) ∧
      (∀ b j, j ≠ i → Disjoint (new b) (S j)) ∧
      (∀ b, Disjoint (new b) Z) ∧
      (new true ∪ new false) \ O = S i \ O ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        (new true ∪ new false) ∩ (g '' convexHull ℝ (a : Set E)) =
          S i ∩ (g '' convexHull ℝ (a : Set E))) ∧
      (new true ∪ new false) ∩ (g '' convexHull ℝ (s : Set E)) =
        (S i ∩ (g '' convexHull ℝ (s : Set E))) \ (Q.symm '' L.boundary ℝ) ∧
      (∃ C₀ : Set X, IsCompact C₀ ∧ C₀ ⊆ O ∧
        (new true ∪ new false) \ C₀ = S i \ C₀ ∧
        C₀ ∩ ((⋃ j, S j) ∩ (g '' convexHull ℝ (s : Set E))) =
          Q.symm '' L.boundary ℝ) ∧
      ∀ b a, a ∈ K.faces → a.card = 2 →
        HasOriginalEdgeCofaceCharts e (new b) K g a := by
  obtain ⟨C, n, L, i, O, new, hLi, hL, hLC, hLint, hO, hOQ, hrO, hOZ,
      hOfaces, hOmembers, ht, htDis, htOther, htZ, hExterior, hOtherFaces,
      hFace, C₀, hC₀, hC₀O, hSupport, hSupportGraph⟩ :=
    exists_protected_positioned_circle_surgery_with_support S sS hdis K N hK hNK
      g hgc hgi hZ hmark hs hs3 Q A hmap hA G hG hGT hphysicalGraph hSZ
      hdim hfinite hinterior hexterior he hcover hQ hcrossings hcircle
  obtain ⟨t⟩ := ht
  refine ⟨C, n, L, i, O, new, hLi, hL, hLC, hLint, hO, hOQ, hrO, hOZ,
    hOfaces, hOmembers, ⟨t⟩, htDis, htOther, htZ, hExterior, hOtherFaces, hFace,
    ⟨C₀, hC₀, hC₀O, hSupport, hSupportGraph⟩, ?_⟩
  intro b a ha ha2
  have hane : a ≠ s := by
    intro heq
    have := congrArg Finset.card heq
    omega
  have hCedge : Disjoint C₀ (g '' convexHull ℝ (a : Set E)) :=
    (hOfaces a ha (by omega) hane).mono_left hC₀O
  have hpair := (hcofaces i a ha ha2).surgery_pair_of_disjoint_support hC₀.isClosed
    (t true).isCompact (t false).isCompact htDis hCedge hSupport
  cases b
  · exact hpair.2
  · exact hpair.1

end PoincareMT.M76
