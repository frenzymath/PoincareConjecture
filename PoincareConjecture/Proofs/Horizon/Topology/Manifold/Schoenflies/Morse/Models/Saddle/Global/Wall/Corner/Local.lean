import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Corner.Frontier

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Corner

theorem frontier_inter_eq_of_inter_eq {A B U : Set E3}
    (hU : IsOpen U) (h : A ∩ U = B ∩ U) :
    frontier A ∩ U = frontier B ∩ U := by
  rw [← frontier_inter_open_inter hU, h, frontier_inter_open_inter hU]

theorem frontier_union_inter_eq_of_corner_coordinates
    {A B U : Set E3} (hU : IsOpen U)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hA : A ∩ U = (D '' leftBody) ∩ U)
    (hB : B ∩ U = (D '' rightBody) ∩ U) :
    frontier (A ∪ B) ∩ U =
      (D '' {p : E3 | p 2 = (p 1)^2 - (p 0)^2}) ∩ U := by
  have hbody : (A ∪ B) ∩ U = (D '' body) ∩ U := by
    rw [union_inter_distrib_right, hA, hB, ← union_inter_distrib_right,
      ← image_union, sides_union]
  have hfront : D '' frontier body = frontier (D '' body) :=
    D.toHomeomorph.image_frontier body
  rw [frontier_inter_eq_of_inter_eq hU hbody, ← hfront, frontier_body]

theorem frontier_sdiff_closure_eq_of_sdiff_eq {A B U : Set E3}
    (h : A \ U = B \ U) :
    frontier A \ closure U = frontier B \ closure U := by
  have hbody : A ∩ (closure U)ᶜ = B ∩ (closure U)ᶜ := by
    ext p
    constructor
    · rintro ⟨hp, hpU⟩
      have hp' : p ∈ A \ U := ⟨hp, fun hu => hpU (subset_closure hu)⟩
      rw [h] at hp'
      exact ⟨hp'.1, hpU⟩
    · rintro ⟨hp, hpU⟩
      have hp' : p ∈ B \ U := ⟨hp, fun hu => hpU (subset_closure hu)⟩
      rw [← h] at hp'
      exact ⟨hp'.1, hpU⟩
  exact frontier_inter_eq_of_inter_eq isClosed_closure.isOpen_compl hbody

theorem sphere_image_sdiff_closure_eq_of_body_agreement
    (a F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) {B U : Set E3}
    (h : (F '' (a '' closedBall (0 : E3) 1)) \ U =
      ((a '' closedBall (0 : E3) 1) ∪ B) \ U) :
    ((a.trans F) '' sphere (0 : E3) 1) \ closure U =
      frontier ((a '' closedBall (0 : E3) 1) ∪ B) \ closure U := by
  have hfront : (a.trans F) '' sphere (0 : E3) 1 =
      frontier (F '' (a '' closedBall (0 : E3) 1)) := by
    calc
      (a.trans F) '' sphere (0 : E3) 1 =
          (a.trans F) '' frontier (closedBall (0 : E3) 1) := by
            rw [frontier_closedBall (0 : E3) (by norm_num : (1 : Real) ≠ 0)]
      _ = frontier ((a.trans F) '' closedBall (0 : E3) 1) :=
        (a.trans F).toHomeomorph.image_frontier _
      _ = frontier (F '' (a '' closedBall (0 : E3) 1)) := by
        rw [Diffeomorph.coe_trans, image_comp]
  rw [hfront]
  exact frontier_sdiff_closure_eq_of_sdiff_eq h

end Poincare.Manifold.Schoenflies.Saddle.Wall.Corner
