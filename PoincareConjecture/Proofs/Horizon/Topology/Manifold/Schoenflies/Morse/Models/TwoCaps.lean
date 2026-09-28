import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.BoundedCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open Poincare.Geometry.Euclidean

theorem boundedCylinderRadius_eq_of_sq_height_eq (v : E3) {p q : S2}
    (h : inner Real v (p : E3) ^ 2 = inner Real v (q : E3) ^ 2) :
    boundedCylinderRadius v p = boundedCylinderRadius v q := by
  unfold boundedCylinderRadius
  congr 2
  change (1 - Real.smoothTransition (4 * inner Real v (p : E3) ^ 2 - 2)) *
      (1 - inner Real v (p : E3) ^ 2) +
      Real.smoothTransition (4 * inner Real v (p : E3) ^ 2 - 2) *
        inner Real v (p : E3) ^ 2 = _
  rw [h]
  rfl

theorem exists_ambient_boundedCylinder_two_caps
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ p : S2, F p = liftPlaneDiffeomorph hv c s hs A
        (boundedCylinderRadius v p • (p : E3))) ∧
      F '' sphere (0 : E3) 1 =
        (liftPlaneDiffeomorph hv c s hs A ''
          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
            {p : S2 | 0 ≤ inner Real v (p : E3)})) ∪
        (liftPlaneDiffeomorph hv c (-s) (neg_ne_zero.mpr hs) A ''
          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
            {p : S2 | 0 ≤ inner Real v (p : E3)})) := by
  let R := (Hemisphere.Plane v).reflection
  have hR (x : E3) : R x = x - (2 * inner Real v x) • v := by
    change (Real ∙ v)ᗮ.reflection x = _
    rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, hv]
    module
  have hRh (x : E3) : inner Real v (R x) = -inner Real v x := by
    rw [hR]
    simp [inner_sub_right, inner_smul_right, hv]
    ring
  have hRp (x : E3) : (Hemisphere.Plane v).orthogonalProjectionOnto (R x) =
      (Hemisphere.Plane v).orthogonalProjectionOnto x := by
    rw [hR]
    simp [Hemisphere.Plane]
  let r : S2 → S2 := fun p => ⟨R p, by
    rw [mem_sphere_zero_iff_norm, R.norm_map, norm_eq_of_mem_sphere]⟩
  have hrh (p : S2) : inner Real v (r p : E3) = -inner Real v (p : E3) := hRh p
  have hrr (p : S2) : r (r p) = p := by
    apply Subtype.ext
    exact (Hemisphere.Plane v).reflection_reflection p
  let b : S2 → E3 := fun p => boundedCylinderRadius v p • (p : E3)
  have hbr (p : S2) : b (r p) = R (b p) := by
    have heq : boundedCylinderRadius v (r p) = boundedCylinderRadius v p :=
      boundedCylinderRadius_eq_of_sq_height_eq v (by rw [hrh, neg_sq])
    change boundedCylinderRadius v (r p) • R (p : E3) = R (boundedCylinderRadius v p • p)
    rw [heq, map_smul]
  let T := liftPlaneDiffeomorph hv c s hs A
  let T' := liftPlaneDiffeomorph hv c (-s) (neg_ne_zero.mpr hs) A
  have hT (x : E3) : T' x = T (R x) := by
    dsimp only [T, T']
    rw [liftPlaneDiffeomorph_apply, liftPlaneDiffeomorph_apply, hRh, hRp]
    congr 2
    ring
  obtain ⟨B, _, hB, _, _⟩ := exists_boundedCylinder_ambient v hv
  let F := B.trans T
  have hF (p : S2) : F p = T (b p) := by
    change T (B p) = _
    rw [hB]
  refine ⟨F, hF, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    let p : S2 := ⟨x, hx⟩
    rw [show F x = T (b p) from hF p]
    by_cases hp : 0 ≤ inner Real v (p : E3)
    · exact Or.inl ⟨b p, ⟨p, hp, rfl⟩, rfl⟩
    · refine Or.inr ⟨b (r p), ⟨r p, ?_, rfl⟩, ?_⟩
      · change 0 ≤ inner Real v (r p : E3)
        rw [hrh]
        linarith
      · rw [hT, ← hbr, hrr]
  · intro y hy
    rcases hy with ⟨z, ⟨p, hp, rfl⟩, rfl⟩ | ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    · exact ⟨p, p.property, hF p⟩
    · refine ⟨r p, (r p).property, ?_⟩
      rw [hF, hbr, ← hT]

theorem exists_ambient_diffeomorph_of_opposite_cap_ranges
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (gPlus gMinus : E2 → E3)
    (hplus : gPlus '' closedBall (0 : E2) 1 = liftPlaneDiffeomorph hv c s hs A ''
      ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
        {p : S2 | 0 ≤ inner Real v (p : E3)}))
    (hminus : gMinus '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv c (-s) (neg_ne_zero.mpr hs) A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)})) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 =
        (gPlus '' closedBall (0 : E2) 1) ∪ (gMinus '' closedBall (0 : E2) 1) := by
  obtain ⟨F, _, hF⟩ := exists_ambient_boundedCylinder_two_caps hv c s hs A
  exact ⟨F, by rw [hplus, hminus]; exact hF⟩

end Poincare.Manifold.Schoenflies
