import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleFreeOtherFaceTransport

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

def InCircleFreeNonreturningTriangleGraphPosition
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (Q : OpenPartialHomeomorph X V3) (S : Set X) (g : E → X)
    (s : Finset E) (A : E →ᴬ[ℝ] V3) : Prop :=
  let T := convexHull ℝ (A '' (s : Set E))
  let t := g '' convexHull ℝ (s : Set E)
  ∃ G : SimplicialComplex ℝ V3,
    G.faces.Finite ∧ G.space ⊆ T ∩ Q.target ∧
    (∀ a ∈ G.faces, a.card ≤ 2) ∧ Q.symm '' G.space = S ∩ t ∧
    (∀ v : G.vertices, (v : V3) ∈ intrinsicInterior ℝ T →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
    (∀ v : G.vertices, (v : V3) ∉ intrinsicInterior ℝ T →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
    (G.space ∩ intrinsicFrontier ℝ T).Finite ∧
    (∀ w ∈ G.space ∩ intrinsicInterior ℝ T,
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0) ∧
    (∀ a : Finset E, a ⊆ s → a.card = 2 →
      ¬ ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set E))) ∧
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ T).Nonempty

theorem InCircleFreeNonreturningTriangleGraphPosition.to_nonreturning
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {Q : OpenPartialHomeomorph X V3} {S : Set X} {g : E → X}
    {s : Finset E} {A : E →ᴬ[ℝ] V3}
    (h : InCircleFreeNonreturningTriangleGraphPosition Q S g s A) :
    InNonreturningTriangleGraphPosition Q S g s A := by
  obtain ⟨G, hG, hGT, hGc, hp, hi, he, hf, hc, hr, _⟩ := h
  exact ⟨G, hG, hGT, hGc, hp, hi, he, hf, hc, hr⟩

theorem InCircleFreeNonreturningTriangleGraphPosition.of_equal_off_closed
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {Q : OpenPartialHomeomorph X V3} {S S' C : Set X} {g : E → X}
    {s : Finset E} {A : E →ᴬ[ℝ] V3}
    (h : InCircleFreeNonreturningTriangleGraphPosition Q S g s A)
    (hC : IsClosed C) (hCt : Disjoint C (g '' convexHull ℝ (s : Set E)))
    (houtside : S' \ C = S \ C) :
    InCircleFreeNonreturningTriangleGraphPosition Q S' g s A := by
  obtain ⟨G, hG, hGT, hGc, hp, hi, he, hf, hc, hr, hfree⟩ := h
  obtain ⟨hp', hc'⟩ := triangle_graph_crossings_of_equal_off_closed Q G
    (hGT.trans inter_subset_right) hp hC hCt houtside hc
  exact ⟨G, hG, hGT, hGc, hp', hi, he, hf, hc', hr, hfree⟩

end PoincareConjecture.M76
