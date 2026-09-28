import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningContactCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningContactChart



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

set_option quotPrecheck false
local notation "P2" => (ℝ × ℝ)
local notation "Rect" => (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
local notation "Ends" => (({0,1} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1)
local notation "Corners" => (({0,1} : Set ℝ) ×ˢ ({-1,1} : Set ℝ))
local notation "Sides" => (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ))




theorem not_spanning_replacement_of_minimal_position
    {X α I : Type*} [TopologicalSpace X] [T2Space X] [Finite I]
    {e : α → OpenPartialHomeomorph X V3} {R D S S' F : Set X}
    (he : PLDomain e R)
    (s' : ChartwisePLSphere e S') (hSR' : S' ⊆ interior R)
    (hn' : ¬∃ B,B ⊆ R ∧ Nonempty (ChartwisePLBall e B S'))
    (Q : OpenPartialHomeomorph X V3) (hDQ : D ⊆ Q.source)
    (hQ : ∀ a,(e a).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {A : Set P2} (p : P2 → X) (hp : PolyhedralPLInCharts e p A)
    (hpi : InjOn p A) (hpD : p '' A ⊆ D)
    (n : I → ℕ) (P : ∀ k,Polygon P2 (n k+3))
    (hP : ∀ k,Function.Injective (P k) ∧ (P k).HasSimplicialEdges)
    (hPA : ∀ k,(P k).boundary ℝ ⊆ A)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    (hcontacts : p '' (⋃ k,(P k).boundary ℝ) = S ∩ F)
    (G : SimplicialComplex ℝ V3) (hG : G.space = Q '' (S ∩ F))
    (i j : I) (hij : i ≠ j) (r : P2 → X)
    (hr : PolyhedralPLInCharts e r Rect) (hri : InjOn r Rect)
    (hrD : r '' Rect ⊆ D)
    (htrace : r '' Rect ∩ (S ∩ F) = r '' Ends)
    (hleft : r (0,0) ∈ p '' (P i).boundary ℝ)
    (hright : r (1,0) ∈ p '' (P j).boundary ℝ)
    (hnew : S' ∩ F = ((S ∩ F) \ (r '' Ends \ r '' Corners)) ∪ r '' Sides)
    (hcross : ∀ x ∈ S' ∩ F,∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ a,(e a).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S' ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ F ↔ H y 0 = 0)
    (hmin : ∀ d : Set X × OpenPartialHomeomorph X V3 × SimplicialComplex ℝ V3,
      (Nonempty (ChartwisePLSphere e d.1) ∧ d.1 ⊆ interior R ∧
        (¬∃ B,B ⊆ R ∧ Nonempty (ChartwisePLBall e B d.1)) ∧
        D ⊆ d.2.1.source ∧
        (∀ a,(e a).symm.trans d.2.1 ∈ piecewiseAffineGroupoid V3) ∧
        d.1 ∩ F ⊆ d.2.1.source ∧
        d.2.2.faces.Finite ∧ d.2.2.space = d.2.1 '' (d.1 ∩ F) ∧
        HasDisjointPolygonPresentation d.2.2.space ∧
        (∀ a ∈ d.2.2.faces,a.card ≤ 2) ∧
        (∀ v : d.2.2.vertices,
          (d.2.2.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
        ∀ w ∈ d.2.2.space,∀ O : Set V3,IsOpen O → w ∈ O →
          ∃ C : OpenPartialHomeomorph V3 C3,
            w ∈ C.source ∧ C.source ⊆ O ∩ d.2.1.target ∧
            (∀ z ∈ C.source,d.2.1.symm z ∈ interior R) ∧ C w = 0 ∧
            LocallyPiecewiseAffineOn C C.source ∧
            LocallyPiecewiseAffineOn C.symm C.target ∧
            (∀ y ∈ C.source,d.2.1.symm y ∈ d.1 ↔ (C y).2 = 0) ∧
            ∀ y ∈ C.source,d.2.1.symm y ∈ F ↔ (C y).1.1 = 0) →
      Nat.card (ConnectedComponents G.space) ≤
        Nat.card (ConnectedComponents d.2.2.space)) : False := by
  classical
  have hpQ : MapsTo p A Q.source := fun x hx => hDQ (hpD ⟨x,hx,rfl⟩)
  have hrQ : MapsTo r Rect Q.source := fun x hx => hDQ (hrD ⟨x,hx,rfl⟩)
  obtain ⟨G',hG',hGs,hpres,hfaces,hdegree,_,hlt⟩ :=
    exists_spanning_contact_graph_in_original_chart Q hQ p hp hpi hpQ n P hP hPA hdis
      hcontacts G hG i j hij r hr hri hrQ htrace hleft hright hnew
  have hCQ : S' ∩ F ⊆ Q.source := by
    intro x hx
    rcases hnew.subset hx with hx | ⟨z,hz,rfl⟩
    · obtain ⟨z,hz,rfl⟩ := hcontacts.symm.subset hx.1
      obtain ⟨k,hk⟩ := mem_iUnion.mp hz
      exact hpQ (hPA k hk)
    · apply hrQ
      refine ⟨hz.1,?_⟩
      rcases hz.2 with h | h
      · norm_num [h]
      · have h' : z.2 = 1 := h
        norm_num [h']
  have hcoord := coordinate_crossings_of_original_paired_charts he hSR' Q hQ hCQ hcross
  apply (Nat.not_le_of_gt hlt)
  apply hmin (S',Q,G')
  exact ⟨⟨s'⟩,hSR',hn',hDQ,hQ,hCQ,hG',hGs,hpres,hfaces,hdegree,
    fun w hw => hcoord w (hGs.subset hw)⟩

end PoincareConjecture.M76


