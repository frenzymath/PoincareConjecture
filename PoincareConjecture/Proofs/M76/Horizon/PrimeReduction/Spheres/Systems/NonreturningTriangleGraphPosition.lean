import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.TriangleGraphPosition








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

def InNonreturningTriangleGraphPosition
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
    ∀ a : Finset E, a ⊆ s → a.card = 2 →
      ¬ ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
            convexHull ℝ (A '' (a : Set E))


theorem InNonreturningTriangleGraphPosition.image_of_fixed
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {Q : OpenPartialHomeomorph X V3} {S : Set X} {g : E → X}
    {s : Finset E} {A : E →ᴬ[ℝ] V3}
    (h : InNonreturningTriangleGraphPosition Q S g s A) (H : X ≃ₜ X)
    {W : Set X} (hW : IsOpen W)
    (htW : g '' convexHull ℝ (s : Set E) ⊆ W) (hfix : EqOn H id W) :
    InNonreturningTriangleGraphPosition Q (H '' S) g s A := by
  obtain ⟨G, hG, hGT, hGc, hphysical, hi, he, hf, hcross, hreturn⟩ := h
  obtain ⟨hp, hc⟩ := triangle_graph_crossings_after_fixed_motion Q H G
    (hGT.trans inter_subset_right) hphysical hW htW hfix hcross
  exact ⟨G, hG, hGT, hGc, hp, hi, he, hf, hc, hreturn⟩

end PoincareConjecture.M76

