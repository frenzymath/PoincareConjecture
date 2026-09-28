import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.CapGeometry
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.CapRange

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

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

open Poincare.Geometry.Euclidean

theorem opposite_cap_union_diff_open_cap
    {v : E3} (hv : ‖v‖ = 1) (b s d : Real) (hs : s ≠ 0) (hd : d ≠ 0)
    (hopposite : s * d < 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (γ : S1 → Hemisphere.Plane v)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (g : E2 → E3) (hgi : Injective g)
    (hcore : g '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v)
    {η : Real} (hη : 0 < η)
    (hcollar : ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
      g (ρ • (q : E2)) = (b + s * capCollarClock ρ) • v + (γ q : E3)) :
    ((liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v) ∪
        (g '' closedBall (0 : E2) 1)) \ (g '' ball (0 : E2) 1) =
      liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v := by
  have hcircle := image_circle_of_cap_collar g γ b s hη hcollar
  have hcircleCap : g '' sphere (0 : E2) 1 ⊆
      liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v := by
    rw [hcircle]
    rintro _ ⟨q, rfl⟩
    obtain ⟨z, hz, he⟩ := hboundary.symm ▸ mem_range_self q
    dsimp only
    rw [← he]
    simpa only [capCoordinates_apply] using
      (transported_cap_boundary_fiber_iff hv b d hd A z
        (mem_sphere_zero_iff_norm.mp hz) b).mpr (by simp)
  have hmeetCircle {y : E3}
      (hy : y ∈ liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v)
      (hyg : y ∈ g '' closedBall (0 : E2) 1) : y ∈ g '' sphere (0 : E2) 1 := by
    have hlow := (transported_cap_bounds hv b d hd A hy).1
    have hhigh := (transported_cap_bounds hv b s hs A (hcore ▸ hyg)).1
    have hzero : inner Real v y = b := by
      rcases lt_or_gt_of_ne hs with hsneg | hspos
      · have hdpos : 0 < d := by nlinarith
        have h₁ := (le_div_iff_of_neg hsneg).mp hhigh
        have h₂ := (le_div_iff₀ hdpos).mp hlow
        linarith
      · have hdneg : d < 0 := by nlinarith
        have h₁ := (le_div_iff₀ hspos).mp hhigh
        have h₂ := (le_div_iff_of_neg hdneg).mp hlow
        linarith
    have hproj := transported_cap_zero_projection hv b d hd A hy hzero
    obtain ⟨q, hq⟩ := hboundary ▸ hproj
    rw [hcircle]
    refine ⟨q, ?_⟩
    have he := (heightCoordinates hv).apply_symm_apply y
    change inner Real v y • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y at he
    rwa [hzero, ← hq] at he
  rw [image_ball_eq_diff_sphere g hgi]
  apply Subset.antisymm
  · rintro y ⟨hy | hyg, hn⟩
    · exact hy
    · apply hcircleCap
      by_contra he
      exact hn ⟨hyg, he⟩
  · intro y hy
    exact ⟨Or.inl hy, fun h => h.2 (hmeetCircle hy h.1)⟩

end Poincare.Manifold.Schoenflies.Reverse

end

end M38Schoenflies
