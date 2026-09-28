import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Replacement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ClosingBall



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)




theorem exists_common_exterior_of_fixed_neighborhood_matching
    (B L H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hball : H '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1)
    {U D : Set E3} (hU : IsOpen U) (hfix : EqOn H id U)
    (hDU : D ⊆ U) (hDB : D ⊆ B '' sphere (0 : E3) 1) :
    ∃ X : Set E3, D ⊆ closure X ∧
      X ⊆ (B '' closedBall (0 : E3) 1)ᶜ ∧ X ⊆ (L '' closedBall (0 : E3) 1)ᶜ := by
  refine ⟨U ∩ (B '' closedBall (0 : E3) 1)ᶜ, ?_, inter_subset_right, ?_⟩
  · intro y hy
    apply hU.inter_closure ⟨hDU hy, ?_⟩
    have hf : y ∈ frontier (B.toHomeomorph '' closedBall (0 : E3) 1) := by
      rw [← B.toHomeomorph.image_frontier, frontier_closedBall _ one_ne_zero]
      exact hDB hy
    rw [← frontier_compl] at hf
    exact frontier_subset_closure hf
  · rintro y ⟨hyU, hyB⟩ hyL
    rw [← hball] at hyL
    obtain ⟨x, hx, he⟩ := hyL
    have hxy : x = y := H.injective (he.trans (hfix hyU).symm)
    exact hyB (hxy ▸ hx)




theorem exists_supported_boundary_replacement_of_fixed_neighborhood_matching
    (B L H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hball : H '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hB : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hL : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    {U : Set E3} (hU : IsOpen U) (hfix : EqOn H id U)
    (hgU : g '' closedBall (0 : E2) r ⊆ U)
    {C : Set E3} (hC : IsClosed C)
    (hBC : (B '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1)
    (hLC : (L '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1) :
    ∃ K W : Set E3, IsCompact K ∧ K ⊆ Cᶜ ∧ IsOpen W ∧
      C ∪ (g '' closedBall (0 : E2) 1) ⊆ W ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, G y = y) ∧ (∀ y ∈ W, G y = y) ∧
        G '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 ∧
        G '' ((B '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1)) =
          (L '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) := by
  obtain ⟨X, hDX, hXB, hXL⟩ := exists_common_exterior_of_fixed_neighborhood_matching
    B L H hball hU hfix hgU hB
  exact Saddle.Caps.exists_supported_boundary_replacement_of_shared_exterior
    B L g hg hgi hgd hr hB hL hDX hXB hXL hC hBC hLC

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
