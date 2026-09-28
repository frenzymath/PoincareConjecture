import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.DisjointClosingBalls
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.NestedClosingBalls

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_ordered_planar_cap_pair
    {v : E3} (hv : ‖v‖ = 1)
    (A : Fin 2 → (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hcircles : Disjoint (A 0 '' sphere (0 : Hemisphere.Plane v) 1) (A 1 '' sphere 0 1)) :
    ∃ σ : Equiv.Perm (Fin 2),
      A (σ 1) '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A (σ 0) '' ball 0 1 ∨
        Disjoint (A (σ 1) '' closedBall (0 : Hemisphere.Plane v) 1) (A (σ 0) '' closedBall 0 1) := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro hz; simp [hz] at hv)).repr
  let : Nontrivial (Hemisphere.Plane v) := Module.nontrivial_of_finrank_pos
    (R := Real) (by rw [J.toLinearEquiv.finrank_eq]; norm_num)
  have hdim : 1 < Module.rank Real (Hemisphere.Plane v) := by
    rw [← Module.finrank_eq_rank, J.toLinearEquiv.finrank_eq]
    norm_num
  rcases (A 0).toHomeomorph.disjoint_or_nested_image_closedBall (A 1).toHomeomorph hdim hcircles
    with hd | h01 | h10
  · exact ⟨Equiv.refl _, Or.inr hd.symm⟩
  · refine ⟨Equiv.swap 0 1, Or.inl ?_⟩
    change A 0 '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A 1 '' ball 0 1 at h01
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using h01
  · exact ⟨Equiv.refl _, Or.inl h10⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
