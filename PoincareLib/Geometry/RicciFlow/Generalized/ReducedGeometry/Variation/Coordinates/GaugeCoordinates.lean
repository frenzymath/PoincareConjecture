import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeLift
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.IntervalLift

/-!
# Regularity of the actual backward gauge coordinates

Morgan-Tian Definition 3.38 and Lemma 6.4, pp. 61, 107-108. The lifted
time coordinate is smooth because its inclusion is the affine backward
clock. The spatial coordinate retains the given curve's C1 regularity.
-/

set_option autoImplicit false
-- Coordinate projections use the supplied cylinder product structure.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)

/-- The actual gauge time coordinate equals the prescribed backward
clock wherever the lift is an inverse, Definition 3.38, p. 61. -/
theorem gaugeLift_time_eq {U : Set G.Point}
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {t : ℝ} (ht : t ∈ Icc τ₁ τ₂) (hsrc : p.curve t ∈ U) :
    (lift (p.curve t)).1.val = T - t :=
  ((G.gaugeCover.cylinder b).time_eq (lift (p.curve t))).symm.trans
    ((congrArg G.spacetime.timeFunction (hright _ hsrc)).trans (p.curve_time t ht))

/-- The actual lifted time coordinate is smooth on every gauge-source
parameter set, even if its image meets a time boundary, Lemma 6.4,
pp. 107-108. -/
theorem gaugeLift_time_contMDiffOn {U : Set G.Point}
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {J : Set ℝ} (hJ : J ⊆ Icc τ₁ τ₂) (hsrc : ∀ t ∈ J, p.curve t ∈ U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ (fun t => (lift (p.curve t)).1) J := by
  apply intervalLift_contMDiffOn (𝓘(ℝ, ℝ))
    (G.timeIntervals.interval (G.gaugeCover.interval b))
  have hc : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => T - t) J :=
    (contDiff_const.sub contDiff_id).contMDiff.contMDiffOn
  exact hc.congr (fun t ht => gaugeLift_time_eq p b lift hright (hJ ht) (hsrc t ht))

/-- The actual spatial coordinate of the lifted path is C1 on every
interior gauge-source parameter set, Lemma 6.4, pp. 107-108. -/
theorem gaugeLift_spatial_contMDiffOn {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    {J : Set ℝ} (hJ : J ⊆ Ioo τ₁ τ₂) (hsrc : ∀ t ∈ J, p.curve t ∈ U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun t => (lift (p.curve t)).2) J := by
  have hL := (hlift.of_le (by simp)).comp (p.curve_regular.mono hJ) hsrc
  exact fun t ht => (hL t ht).snd

/-- The included spatial coordinate has the actual Euclidean C1
regularity needed by the quadratic variational argument, Lemma 6.4,
pp. 107-108. -/
theorem gaugeLift_spatial_contDiffOn {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    {J : Set ℝ} (hJ : J ⊆ Ioo τ₁ τ₂) (hsrc : ∀ t ∈ J, p.curve t ∈ U) :
    ContDiffOn ℝ 1 (fun t => (lift (p.curve t)).2.val) J := by
  have hv : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) := contMDiff_subtype_val
  exact ((hv.of_le (by simp)).comp_contMDiffOn
    (gaugeLift_spatial_contMDiffOn p b lift hlift hJ hsrc)).contDiffOn

end PoincareMT.M14
