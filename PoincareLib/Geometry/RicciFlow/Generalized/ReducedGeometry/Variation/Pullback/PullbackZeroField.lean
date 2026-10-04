import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.PullbackLinearity

/-!
# A zero actual field has zero covariant derivative

Morgan-Tian Lemma 6.4, pp. 107-108. Affine linearity of the actual
pullback derivative forces every extension of a zero field to have
zero derivative, including closed endpoints with unique derivatives.
-/

set_option autoImplicit false

open Set
open scoped Manifold

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}

/-- Every actual extension of a zero field has zero covariant
derivative along an arbitrary differentiable base curve,
Lemma 6.4, pp. 107-108. -/
theorem horizontalCovariantDerivative_zero_field
    (E : M14PullbackExtension G γ J Y) (hY : ∀ r ∈ J, Y r = 0)
    {s : ℝ} (hs : s ∈ J) (hJ : UniqueDiffWithinAt ℝ J s)
    (hγ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s) :
    M14HorizontalCovariantDerivative G γ J Y E s = 0 := by
  have h := horizontalCovariantDerivative_affine_congr E E E (1 : ℝ)
    (fun r hr => by rw [hY r hr, smul_zero, add_zero]) hs hJ hγ
  rw [one_smul] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

end PoincareMT.M14
