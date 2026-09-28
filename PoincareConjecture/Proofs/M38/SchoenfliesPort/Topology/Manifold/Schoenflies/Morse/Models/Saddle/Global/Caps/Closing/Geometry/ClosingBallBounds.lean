import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.CurvedCapSeparation
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.CapBody
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.FilledSides
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Side.Filled

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem curved_closing_ball_height_le
    {v : E3} (hv : ‖v‖ = 1) (b w : Real) (hw : 0 < w)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (B Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    {E : Set E3} (hE : ∀ y ∈ E, inner Real v y ≤ b)
    (hB : B '' sphere (0 : E3) 1 = E ∪
      Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v)) :
    ∀ y ∈ B '' closedBall (0 : E3) 1, inner Real v y ≤ b + 2 * w := by
  have hsurj : Surjective (innerSL Real v) := by
    intro t
    refine ⟨t • v, ?_⟩
    simp [hv]
  apply Saddle.Wall.Side.coordinate_bound_of_frontier_bound
    ((isCompact_closedBall (0 : E3) 1).image B.continuous)
    (innerSL Real v) (innerSL Real v).continuous ((innerSL Real v).isOpenMap hsurj)
  intro y hy
  change y ∈ frontier (B.toHomeomorph '' closedBall (0 : E3) 1) at hy
  rw [← B.toHomeomorph.image_frontier, frontier_closedBall _ one_ne_zero] at hy
  change y ∈ B '' sphere (0 : E3) 1 at hy
  rw [hB] at hy
  rcases hy with hy | ⟨z, hz, rfl⟩
  · have hh := hE y hy
    change inner Real v y ≤ _
    linarith
  · have hh := (abs_le.mp (Reverse.transported_cap_bounds hv b w hw.ne' A hz).2.2).2
    rw [abs_of_pos hw] at hh
    have hinv : inner Real v (Q.symm z) = inner Real v z := by
      rw [← hQ (Q.symm z), Q.apply_symm_apply]
    change inner Real v (Q.symm z) ≤ _
    rw [hinv]
    linarith

theorem closing_ball_projection_mem_filling
    {v : E3}
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hboundary : ∀ y ∈ B '' sphere (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1) :
    ∀ y ∈ B '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 := by
  let P := (Hemisphere.Plane v).orthogonalProjectionOnto
  have hsurj : Surjective P := fun x => ⟨x, by simp [P]⟩
  have hb := Reverse.norm_le_on_filled_ball_of_boundary_bound B.toHomeomorph
    (fun y => A.symm (P y)) (A.symm.continuous.comp P.continuous)
    (A.symm.toHomeomorph.isOpenMap.comp (P.isOpenMap hsurj)) zero_le_one (by
      intro y hy
      obtain ⟨q, hq, heq⟩ := hboundary y hy
      rw [← heq, A.symm_apply_apply]
      exact mem_closedBall_zero_iff.mp hq)
  intro y hy
  exact ⟨A.symm (P y), mem_closedBall_zero_iff.mpr (hb y hy), A.apply_symm_apply _⟩

theorem prepared_closing_ball_projection_mem_filling
    {v : E3} {b : Real}
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (B N Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hN : EqOn N Q {y | b ≤ inner Real v y})
    (hboundary : ∀ y ∈ (B.trans N) '' sphere (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1)
    {y : E3} (hy : y ∈ B '' closedBall (0 : E3) 1) (hheight : b ≤ inner Real v y) :
    (Hemisphere.Plane v).orthogonalProjectionOnto (Q y) ∈ A '' closedBall 0 1 := by
  rw [← hN hheight]
  apply closing_ball_projection_mem_filling A (B.trans N) hboundary
  change N y ∈ (N ∘ B) '' closedBall (0 : E3) 1
  rw [image_comp]
  exact mem_image_of_mem N hy

theorem closing_ball_inter_band_subset_closing_disk
    {v : E3} {b c : Real}
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (B N Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {E Δ band : Set E3}
    (hB : B '' sphere (0 : E3) 1 = E ∪ Δ)
    (hN : EqOn N Q {y | b ≤ inner Real v y})
    (hprojection : ∀ y ∈ (B.trans N) '' sphere (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1)
    (hheight : ∀ y ∈ B '' closedBall (0 : E3) 1, inner Real v y ≤ c)
    (hband : ∀ y ∈ band, b ≤ inner Real v y)
    (havoid : ∀ y ∈ band, inner Real v y ≤ c →
      (Hemisphere.Plane v).orthogonalProjectionOnto (Q y) ∉ A '' ball 0 1)
    (hattach : E ∩ band ⊆ Δ) :
    (B '' closedBall (0 : E3) 1) ∩ band ⊆ Δ := by
  rintro y ⟨hy, hyband⟩
  have hnopen : y ∉ B '' ball (0 : E3) 1 := by
    intro hyopen
    have hNopen : N y ∈ (B.trans N) '' ball (0 : E3) 1 := by
      change N y ∈ (N ∘ B) '' ball (0 : E3) 1
      rw [image_comp]
      exact mem_image_of_mem N hyopen
    have hp := Reverse.projection_mem_open_disk_of_mem_open_body A (B.trans N).toHomeomorph
      (closing_ball_projection_mem_filling A (B.trans N) hprojection) hNopen
    rw [hN (hband y hyband)] at hp
    exact havoid y hyband (hheight y hy) hp
  have hboundary : y ∈ B '' sphere (0 : E3) 1 := by
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, mem_sphere_zero_iff_norm.mpr ?_, rfl⟩
    exact le_antisymm (mem_closedBall_zero_iff.mp hx)
      (le_of_not_gt (fun hh => hnopen ⟨x, mem_ball_zero_iff.mpr hh, rfl⟩))
  rw [hB] at hboundary
  exact hboundary.elim (fun hh => hattach ⟨hh, hyband⟩) id

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
