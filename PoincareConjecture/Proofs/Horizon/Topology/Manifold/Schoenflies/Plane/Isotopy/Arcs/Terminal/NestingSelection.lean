import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.CircleMatching

noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open Plane.Isotopy.ArcPairs
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

theorem nestedPair_asymm_of_smooth
    (C D : S1 → E2)
    (hC : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ C)
    (hD : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ D)
    (hCD : NestedPair C D) : ¬ NestedPair D C := by
  intro hDC
  obtain ⟨A, hA⟩ := exists_ambient_diffeomorph_of_smooth_circle C hC
  obtain ⟨B, hB⟩ := exists_ambient_diffeomorph_of_smooth_circle D hD
  have hAB := (nestedPair_iff_of_normalizations C D A B hA hB).mp hCD
  have hBA := (nestedPair_iff_of_normalizations D C B A hB hA).mp hDC
  let q : E2 := EuclideanSpace.single 0 1
  have hq : q ∈ sphere (0 : E2) 1 := by simp [q]
  have hqA : A q ∈ A '' closedBall 0 1 := mem_image_of_mem A (sphere_subset_closedBall hq)
  have hqAopen := hBA ((image_mono ball_subset_closedBall) (hAB hqA))
  obtain ⟨x, hx, hxeq⟩ := hqAopen
  have hxq := A.injective hxeq
  subst x
  exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hq)

theorem exists_circle_candidate_with_matching_nesting
    (C : Fin 2 → S1 → E2) (D : Fin 3 → Fin 2 → S1 → E2)
    (hC : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i))
    (hD : ∀ k i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (D k i))
    (hzero : ¬ NestedPair (D 0 0) (D 0 1))
    (hzero' : ¬ NestedPair (D 0 1) (D 0 0))
    (hone : NestedPair (D 1 0) (D 1 1) ∨ NestedPair (D 1 1) (D 1 0))
    (hflip : (NestedPair (D 2 0) (D 2 1) ↔ NestedPair (D 1 1) (D 1 0)) ∧
      (NestedPair (D 2 1) (D 2 0) ↔ NestedPair (D 1 0) (D 1 1))) :
    ∃ k : Fin 3, ∀ i j : Fin 2, i ≠ j →
      (NestedPair (C i) (C j) ↔ NestedPair (D k i) (D k j)) := by
  classical
  have hCa := nestedPair_asymm_of_smooth (C 0) (C 1) (hC 0) (hC 1)
  have hCb := nestedPair_asymm_of_smooth (C 1) (C 0) (hC 1) (hC 0)
  have hDa := nestedPair_asymm_of_smooth (D 1 0) (D 1 1) (hD 1 0) (hD 1 1)
  have hDb := nestedPair_asymm_of_smooth (D 1 1) (D 1 0) (hD 1 1) (hD 1 0)
  have hchoose (k : Fin 3)
      (h01 : NestedPair (C 0) (C 1) ↔ NestedPair (D k 0) (D k 1))
      (h10 : NestedPair (C 1) (C 0) ↔ NestedPair (D k 1) (D k 0)) :
      ∃ k : Fin 3, ∀ i j : Fin 2, i ≠ j →
        (NestedPair (C i) (C j) ↔ NestedPair (D k i) (D k j)) := by
    refine ⟨k, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h01
    · exact h10
    · exact (hij rfl).elim
  by_cases h01 : NestedPair (C 0) (C 1)
  · rcases hone with hd01 | hd10
    · apply hchoose 1 <;> tauto
    · apply hchoose 2 <;> tauto
  · by_cases h10 : NestedPair (C 1) (C 0)
    · rcases hone with hd01 | hd10
      · apply hchoose 2 <;> tauto
      · apply hchoose 1 <;> tauto
    · apply hchoose 0 <;> tauto

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
