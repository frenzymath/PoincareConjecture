import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.BodyBounds
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.CapGeometry







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Reverse
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem filled_ball_cylinder_bounds
    {v : E3} (hv : ‖v‖ = 1) (b c : Real) (hc : 0 ≤ c)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hboundary : ∀ y ∈ B '' sphere (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
        |inner Real v y - b| ≤ c) :
    ∀ y ∈ B '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
        |inner Real v y - b| ≤ c := by
  let P := (Hemisphere.Plane v).orthogonalProjectionOnto
  have hsurj : Surjective P := fun x => ⟨x, by simp [P]⟩
  have hproj := norm_le_on_filled_ball_of_boundary_bound B.toHomeomorph
    (fun y => A.symm (P y)) (A.symm.continuous.comp P.continuous)
    (A.symm.toHomeomorph.isOpenMap.comp (P.isOpenMap hsurj)) zero_le_one (by
      intro y hy
      obtain ⟨q, hq, he⟩ := (hboundary y hy).1
      rw [← he, A.symm_apply_apply]
      exact mem_closedBall_zero_iff.mp hq)
  have hheightSurj : Surjective (innerSL Real v) := by
    intro t
    refine ⟨t • v, ?_⟩
    simp [hv]
  have hopen : IsOpenMap (fun y : E3 => inner Real v y - b) := by
    convert! (Homeomorph.addRight (-b)).isOpenMap.comp
      ((innerSL Real v).isOpenMap hheightSurj) using 1
  have hheight := norm_le_on_filled_ball_of_boundary_bound B.toHomeomorph
    (fun y => inner Real v y - b) ((innerSL Real v).continuous.sub continuous_const)
    hopen hc (by
      intro y hy
      rw [Real.norm_eq_abs]
      exact (hboundary y hy).2)
  intro y hy
  refine ⟨⟨A.symm (P y), mem_closedBall_zero_iff.mpr (hproj y hy),
    A.apply_symm_apply (P y)⟩, ?_⟩
  simpa only [Real.norm_eq_abs] using hheight y hy

end Poincare.Manifold.Schoenflies.Reverse

end

end M38Schoenflies
