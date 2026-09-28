import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.FaceGraphTransport

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

def InTriangleGraphPosition {X : Type*} [TopologicalSpace X]
    (Q : OpenPartialHomeomorph X V3) (S t : Set X) (T : Set V3) : Prop :=
  ∃ G : SimplicialComplex ℝ V3,
    G.faces.Finite ∧ G.space ⊆ T ∩ Q.target ∧
    (∀ a ∈ G.faces, a.card ≤ 2) ∧ Q.symm '' G.space = S ∩ t ∧
    (∀ v : G.vertices, (v : V3) ∈ intrinsicInterior ℝ T →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
    (∀ v : G.vertices, (v : V3) ∉ intrinsicInterior ℝ T →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
    (G.space ∩ intrinsicFrontier ℝ T).Finite ∧
    ∀ w ∈ G.space ∩ intrinsicInterior ℝ T,
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0

theorem InTriangleGraphPosition.image_of_fixed
    {X : Type*} [TopologicalSpace X]
    {Q : OpenPartialHomeomorph X V3} {S t : Set X} {T : Set V3}
    (h : InTriangleGraphPosition Q S t T) (H : X ≃ₜ X)
    {W : Set X} (hW : IsOpen W) (htW : t ⊆ W) (hfix : EqOn H id W) :
    InTriangleGraphPosition Q (H '' S) t T := by
  obtain ⟨G, hG, hGT, hGc, hphysical, hi, he, hf, hcross⟩ := h
  obtain ⟨hp, hc⟩ := triangle_graph_crossings_after_fixed_motion Q H G
    (hGT.trans inter_subset_right) hphysical hW htW hfix hcross
  exact ⟨G, hG, hGT, hGc, hp, hi, he, hf, hc⟩

end PoincareConjecture.M76
