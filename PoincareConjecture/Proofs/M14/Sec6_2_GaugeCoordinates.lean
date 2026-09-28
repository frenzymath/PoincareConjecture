import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Proofs.M14.Sec6_2_IntervalLift

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)

theorem gaugeLift_time_eq {U : Set G.Point}
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {t : ℝ} (ht : t ∈ Icc τ₁ τ₂) (hsrc : p.curve t ∈ U) :
    (lift (p.curve t)).1.val = T - t :=
  ((G.gaugeCover.cylinder b).time_eq (lift (p.curve t))).symm.trans
    ((congrArg G.spacetime.timeFunction (hright _ hsrc)).trans (p.curve_time t ht))

theorem gaugeLift_time_contMDiffOn {U : Set G.Point}
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {J : Set ℝ} (hJ : J ⊆ Icc τ₁ τ₂) (hsrc : ∀ t ∈ J, p.curve t ∈ U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ (fun t => (lift (p.curve t)).1) J := by
  apply intervalLift_contMDiffOn (𝓘(ℝ, ℝ))
    (G.timeIntervals.interval (G.gaugeCover.interval b))
  have hc : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => T - t) J :=
    (contDiff_const.sub contDiff_id).contMDiff.contMDiffOn
  exact hc.congr (fun t ht => gaugeLift_time_eq p b lift hright (hJ ht) (hsrc t ht))

theorem gaugeLift_spatial_contMDiffOn {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    {J : Set ℝ} (hJ : J ⊆ Ioo τ₁ τ₂) (hsrc : ∀ t ∈ J, p.curve t ∈ U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun t => (lift (p.curve t)).2) J := by
  have hL := (hlift.of_le (by simp)).comp (p.curve_regular.mono hJ) hsrc
  exact fun t ht => (hL t ht).snd

theorem gaugeLift_spatial_contDiffOn {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    {J : Set ℝ} (hJ : J ⊆ Ioo τ₁ τ₂) (hsrc : ∀ t ∈ J, p.curve t ∈ U) :
    ContDiffOn ℝ 1 (fun t => (lift (p.curve t)).2.val) J := by
  have hv : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) := contMDiff_subtype_val
  exact ((hv.of_le (by simp)).comp_contMDiffOn
    (gaugeLift_spatial_contMDiffOn p b lift hlift hJ hsrc)).contDiffOn

end PoincareConjecture.M14
