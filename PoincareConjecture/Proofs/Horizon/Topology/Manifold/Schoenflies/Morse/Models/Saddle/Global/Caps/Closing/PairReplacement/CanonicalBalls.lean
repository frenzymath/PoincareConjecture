import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.PairReplacement.CanonicalGeometry
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.PairReplacement.Curved
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.NormalizedBoundary



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)




theorem exists_ordered_canonical_closing_balls
    {v : E3} (hv : ‖v‖ = 1)
    (A : Fin 2 → (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (b : Real) (w : Fin 2 → Real) (hw : ∀ i, 0 < w i)
    (hposition : A 1 '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A 0 '' ball 0 1 ∨
      Disjoint (A 1 '' closedBall (0 : Hemisphere.Plane v) 1) (A 0 '' closedBall 0 1))
    (hscale : A 1 '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A 0 '' ball 0 1 → 2 * w 1 < w 0)
    (E : Fin 2 → Set E3) (hEdis : Disjoint (E 0) (E 1))
    (hEheight : ∀ i, ∀ y ∈ E i, inner Real v y ≤ b)
    (a s : Fin 2 → Real) (ha : ∀ i, a i < b) (hs : ∀ i, s i < 0)
    (N : Fin 2 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    {η : Real} (hη : 0 < η)
    (hN : ∀ i, EqOn (N i) Q {y | b - η ≤ inner Real v y})
    (himage : ∀ i, N i '' E i =
      liftPlaneDiffeomorph hv (a i) (s i) (hs i).ne (A i) '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A i '' sphere (0 : Hemisphere.Plane v) 1) (a i) b) :
    ∃ B : Fin 2 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ i, B i '' sphere (0 : E3) 1 = E i ∪
        Q.symm '' (liftPlaneDiffeomorph hv b (w i) (hw i).ne' (A i) '' boundedCylinderNorthernCap v)) ∧
      (B 1 '' closedBall (0 : E3) 1 ⊆ B 0 '' ball (0 : E3) 1 ∨
        Disjoint (B 1 '' closedBall (0 : E3) 1) (B 0 '' closedBall (0 : E3) 1)) := by
  classical
  have hNhalf (i : Fin 2) : EqOn (N i) Q {y | b ≤ inner Real v y} := by
    intro y hy
    exact hN i (by change b - η ≤ inner Real v y; change b ≤ inner Real v y at hy; linarith)
  have hex (i : Fin 2) := exists_curved_closing_ball_of_lower_cap_normalization hv (A i)
    (ha i).le (hs i) (hw i) (N i) Q hQ (hNhalf i) (himage i)
  choose B hB using hex
  refine ⟨B, hB, ?_⟩
  rcases hposition with hn | hd
  · obtain ⟨I, O, hI, hO, hIO⟩ := exists_strictly_nested_curved_closing_balls hv (A 1) (A 0)
      (ha 1).le (ha 0).le (hs 1) (hs 0) (hw 1) (hw 0) hn (hscale hn)
      (N 1) (N 0) Q hQ (hNhalf 1) (hNhalf 0) hEdis.symm (hEheight 1) (hEheight 0)
      (himage 1) (himage 0)
    have hdim : 1 < Module.rank Real E3 := by rw [← Module.finrank_eq_rank]; norm_num
    have hinner : B 1 '' closedBall (0 : E3) 1 = I '' closedBall (0 : E3) 1 :=
      (B 1).toHomeomorph.image_closedBall_eq_of_image_sphere_eq I.toHomeomorph hdim
        ((hB 1).trans hI.symm)
    have houter : B 0 '' ball (0 : E3) 1 = O '' ball (0 : E3) 1 :=
      (B 0).toHomeomorph.image_ball_eq_of_image_sphere_eq O.toHomeomorph hdim
        ((hB 0).trans hO.symm)
    exact Or.inl (by rw [hinner, houter]; exact hIO)
  · apply Or.inr
    have hΔheight (i : Fin 2) :
        ∀ y ∈ Q.symm '' (liftPlaneDiffeomorph hv b (w i) (hw i).ne' (A i) ''
          boundedCylinderNorthernCap v), b ≤ inner Real v y := by
      rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hQi (z : E3) : inner Real v (Q.symm z) = inner Real v z := by
        rw [← hQ (Q.symm z), Q.apply_symm_apply]
      rw [hQi, inner_liftPlaneDiffeomorph]
      exact le_add_of_nonneg_right (mul_nonneg (hw i).le
        (height_nonneg_of_mem_boundedCylinderNorthernCap hx))
    have hrim (i : Fin 2) := closing_rim_subset_of_canonical_cylinder hv (A i) (ha i) (hw i)
      hη (N i) Q hQ (hN i) (by rw [himage i]; exact subset_union_right)
    have hΔdis : Disjoint
        (Q.symm '' (liftPlaneDiffeomorph hv b (w 1) (hw 1).ne' (A 1) '' boundedCylinderNorthernCap v))
        (Q.symm '' (liftPlaneDiffeomorph hv b (w 0) (hw 0).ne' (A 0) '' boundedCylinderNorthernCap v)) :=
      (disjoint_image_iff Q.symm.injective).mpr
        (disjoint_curved_closing_caps_of_disjoint_fillings hv b (w 1) (w 0) (hw 1) (hw 0)
          (A 1) (A 0) hd)
    have hbdis : Disjoint (B 1 '' sphere (0 : E3) 1) (B 0 '' sphere (0 : E3) 1) := by
      rw [hB 1, hB 0]
      exact disjoint_closed_cap_boundaries hEdis.symm hΔdis (hEheight 1) (hEheight 0)
        (hΔheight 1) (hΔheight 0) (fun _ hy hh => hrim 1 ⟨hy, hh⟩)
        (fun _ hy hh => hrim 0 ⟨hy, hh⟩)
    exact disjoint_closing_balls_of_disjoint_prepared_fillings hv b (w 1) (w 0) (hw 1) (hw 0)
      (A 1) (A 0) (B 1) (B 0) (N 1) (N 0) Q hQ (hNhalf 1) (hNhalf 0)
      (by rw [hB 1]; exact subset_union_right) (by rw [hB 0]; exact subset_union_right)
      (normalized_curved_closing_boundary_projection hv (A 1) (hs 1) (hw 1)
        (B 1) (N 1) Q hQ (hNhalf 1) (himage 1) (hB 1))
      (normalized_curved_closing_boundary_projection hv (A 0) (hs 0) (hw 0)
        (B 0) (N 0) Q hQ (hNhalf 0) (himage 0) (hB 0)) hbdis hd

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
