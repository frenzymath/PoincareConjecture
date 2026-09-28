import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryCrossings
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NonreturningTriangleGraphPosition










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem face_inter_eq_of_equal_off_support
    {X : Type*} {S S' C t : Set X}
    (houtside : S' \ C = S \ C) (hCt : Disjoint C t) : S' ∩ t = S ∩ t := by
  ext x
  by_cases hxt : x ∈ t
  · have hxC : x ∉ C := fun hx => Set.disjoint_left.mp hCt hx hxt
    have hmem : x ∈ S' ↔ x ∈ S := by
      simpa only [mem_sdiff, hxC, not_false_eq_true, and_true] using
        Set.ext_iff.mp houtside x
    simpa only [mem_inter_iff, hxt, and_true] using hmem
  · simp only [mem_inter_iff, hxt, and_false]


theorem triangle_graph_crossings_of_equal_off_closed
    {X : Type*} [TopologicalSpace X]
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    {S S' C t : Set X} {T : Set V3}
    (hGT : G.space ⊆ Q.target) (hphysical : Q.symm '' G.space = S ∩ t)
    (hC : IsClosed C) (hCt : Disjoint C t) (houtside : S' \ C = S \ C)
    (hcrossing : ∀ w ∈ G.space ∩ intrinsicInterior ℝ T,
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0) :
    Q.symm '' G.space = S' ∩ t ∧
    ∀ w ∈ G.space ∩ intrinsicInterior ℝ T,
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ S' ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0 := by
  refine ⟨hphysical.trans (face_inter_eq_of_equal_off_support houtside hCt).symm, ?_⟩
  intro w hw
  have hwt : Q.symm w ∈ t := (hphysical.subset ⟨w, hw.1, rfl⟩).2
  have hwC : Q.symm w ∉ C := fun hx => Set.disjoint_left.mp hCt hx hwt
  exact paired_face_crossings_of_equal_off_closed Q hC houtside (hGT hw.1) hwC
    (hcrossing w hw)

theorem InNonreturningTriangleGraphPosition.of_equal_off_closed
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {Q : OpenPartialHomeomorph X V3} {S S' C : Set X} {g : E → X}
    {s : Finset E} {A : E →ᴬ[ℝ] V3}
    (h : InNonreturningTriangleGraphPosition Q S g s A)
    (hC : IsClosed C) (hCt : Disjoint C (g '' convexHull ℝ (s : Set E)))
    (houtside : S' \ C = S \ C) :
    InNonreturningTriangleGraphPosition Q S' g s A := by
  obtain ⟨G, hG, hGT, hGc, hphysical, hi, he, hf, hcross, hreturn⟩ := h
  obtain ⟨hp, hc⟩ := triangle_graph_crossings_of_equal_off_closed Q G
    (hGT.trans inter_subset_right) hphysical hC hCt houtside hcross
  exact ⟨G, hG, hGT, hGc, hp, hi, he, hf, hc, hreturn⟩

end PoincareConjecture.M76
