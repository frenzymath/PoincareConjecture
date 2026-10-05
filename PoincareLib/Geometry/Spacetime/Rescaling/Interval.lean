import PoincareLib.Geometry.Spacetime.Interval
import PoincareLib.Geometry.Spacetime.Rescaling.Time
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M13IntervalGeometry.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Actual affine transport of selected interval geometry

Morgan-Tian Definition 3.40, p. 61. The subtype maps preserve the exact
interval domains. M13 produces their smooth diffeomorphisms within one
selected interval system. Derivative factors refer to positive actual time
tangents, including at a right endpoint whose chart orientation is reversed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

namespace PoincareMT

/-- The actual forward time map on the exact interval subtypes. -/
noncomputable def parabolicTimePoint (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) : I.domain → (parabolicInterval Q hQ a I).domain :=
  fun t ↦ ⟨parabolicTime Q a t.val,
    (parabolicTime_mem_parabolicInterval_iff Q hQ a I t.val).2 t.property⟩

/-- The actual inverse time map on the exact interval subtypes. -/
noncomputable def parabolicTimePointInv (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) : (parabolicInterval Q hQ a I).domain → I.domain :=
  fun s ↦ ⟨parabolicTimeInv Q a s.val,
    (mem_parabolicInterval_iff Q hQ a I s.val).1 s.property⟩

@[simp]
theorem parabolicTimePoint_val (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) (t : I.domain) :
    (parabolicTimePoint Q hQ a I t).val = parabolicTime Q a t.val := rfl

@[simp]
theorem parabolicTimePointInv_val (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) (s : (parabolicInterval Q hQ a I).domain) :
    (parabolicTimePointInv Q hQ a I s).val = parabolicTimeInv Q a s.val := rfl

/-- Affine images retain every true inclusion of the original time intervals. -/
theorem parabolicInterval_subset (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I J : SpacetimeInterval) (h : I.domain ⊆ J.domain) :
    (parabolicInterval Q hQ a I).domain ⊆ (parabolicInterval Q hQ a J).domain :=
  Set.image_mono h

/-- M13's smooth affine interval transport in one selected interval system.
Existence is a theorem output; these data are not constructed by an admission. -/
structure ParabolicIntervalTransport (T : SpacetimeIntervalSystem)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) where
  diffeomorph : ∀ I : SpacetimeInterval,
    Diffeomorph (𝓡∂ 1) (𝓡∂ 1) (T.interval I).Point
      (T.interval (parabolicInterval Q hQ a I)).Point ∞
  forward_eq : ∀ (I : SpacetimeInterval) (t : (T.interval I).Point),
    diffeomorph I t = parabolicTimePoint Q hQ a I t
  inverse_eq : ∀ (I : SpacetimeInterval)
    (s : (T.interval (parabolicInterval Q hQ a I)).Point),
    (diffeomorph I).symm s = parabolicTimePointInv Q hQ a I s
  derivative : ∀ (I : SpacetimeInterval) (t : (T.interval I).Point),
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (diffeomorph I) t ((T.interval I).positiveTangent t) =
      Q • (T.interval (parabolicInterval Q hQ a I)).positiveTangent (diffeomorph I t)
  inverse_derivative : ∀ (I : SpacetimeInterval)
    (s : (T.interval (parabolicInterval Q hQ a I)).Point),
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (diffeomorph I).symm s
      ((T.interval (parabolicInterval Q hQ a I)).positiveTangent s) =
        (1 / Q : ℝ) • (T.interval I).positiveTangent ((diffeomorph I).symm s)

namespace ParabolicIntervalTransport

variable {T : SpacetimeIntervalSystem} {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

/-- The actual forward affine maps commute with interval restriction. -/
theorem inclusion_commutes (P : ParabolicIntervalTransport T Q hQ a)
    (I J : SpacetimeInterval) (h : I.domain ⊆ J.domain) (t : (T.interval I).Point) :
    P.diffeomorph J (spacetimeIntervalInclusion (T.interval I) (T.interval J) h t) =
      spacetimeIntervalInclusion (T.interval (parabolicInterval Q hQ a I))
        (T.interval (parabolicInterval Q hQ a J)) (parabolicInterval_subset Q hQ a I J h)
        (P.diffeomorph I t) := by
  rw [P.forward_eq J, P.forward_eq I]
  rfl

/-- The actual inverse affine maps commute with interval restriction. -/
theorem inverse_inclusion_commutes (P : ParabolicIntervalTransport T Q hQ a)
    (I J : SpacetimeInterval) (h : I.domain ⊆ J.domain)
    (s : (T.interval (parabolicInterval Q hQ a I)).Point) :
    (P.diffeomorph J).symm
      (spacetimeIntervalInclusion (T.interval (parabolicInterval Q hQ a I))
        (T.interval (parabolicInterval Q hQ a J)) (parabolicInterval_subset Q hQ a I J h) s) =
      spacetimeIntervalInclusion (T.interval I) (T.interval J) h ((P.diffeomorph I).symm s) := by
  rw [P.inverse_eq J, P.inverse_eq I]
  rfl

end ParabolicIntervalTransport

end PoincareMT
