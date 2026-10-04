import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.AdaptedFields.UnitAdaptedField
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.MovingMetric
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Metric conservation for actual adapted factors

The actual Ricci correction cancels the square-time metric defect.
Pairings are constant on every closed interval, and positive definiteness
gives uniqueness from any interval point. Morgan-Tian Lemma 6.36, p. 122.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p} {a b : ℝ} {P Q : ∀ s, G.Horizontal (R.curve s)}

set_option backward.isDefEq.respectTransparency false in
-- The scalar clock tangent fiber is the actual real model.
/-- The actual pairing of two unit-adapted fields has zero within
derivative, including at both endpoints, Lemma 6.36, p. 122. -/
theorem horizontalUnitAdapted_pair_hasDerivWithinAt
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hP : IsHorizontalUnitAdaptedFieldOn R a b P)
    (hQ : IsHorizontalUnitAdaptedFieldOn R a b Q) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivWithinAt (fun r => G.spacetime.horizontalMetric.inner (R.curve r) (P r) (Q r))
      0 (Icc a b) s := by
  obtain ⟨E, hE⟩ := hP.equation
  obtain ⟨F, hF⟩ := hQ.equation
  have hR := R.smooth.mono R.interval_subset
  have hJ := uniqueDiffOn_Icc hP.ordered s hs
  have hclock : (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
      G.spacetime.timeFunction (R.curve s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) R.curve (Icc a b) s (1 : ℝ))) =
        -(2 * s) := by
    rw [mfderivWithin_subset hP.interval_subset hJ.uniqueMDiffWithinAt
      ((hR s (hP.interval_subset hs)).mdifferentiableWithinAt (by simp))]
    exact squareRoot_velocity_clock R (hP.interval_subset hs)
  have hd := horizontalCovariantDerivative_metric_product E F hs hJ
    (((hR.mono hP.interval_subset) s hs).mdifferentiableWithinAt (by simp))
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  rw [hclock, G.spacetime.horizontalMetric.symm (R.curve s) (P s),
    hE s hs, hF s hs, H.ricci_symmetric (R.curve s) (Q s)] at hd
  convert hd using 1
  ring

/-- Actual unit-adapted pairings are constant throughout the closed
interval, the nonsingular form of Lemma 6.36, p. 122. -/
theorem horizontalUnitAdapted_pair_eq (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hP : IsHorizontalUnitAdaptedFieldOn R a b P)
    (hQ : IsHorizontalUnitAdaptedFieldOn R a b Q)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    G.spacetime.horizontalMetric.inner (R.curve t) (P t) (Q t) =
      G.spacetime.horizontalMetric.inner (R.curve s) (P s) (Q s) := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => horizontalUnitAdapted_pair_hasDerivWithinAt hM12 hP hQ hr)
    (C := 0) (fun _ _ => by simp) hs ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h

/-- Actual unit-adapted fields agreeing at any one interval point
agree on the whole closed interval, by Lemma 6.36, p. 122. -/
theorem horizontalUnitAdapted_unique (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hP : IsHorizontalUnitAdaptedFieldOn R a b P)
    (hQ : IsHorizontalUnitAdaptedFieldOn R a b Q)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (heq : P t₀ = Q t₀) :
    ∀ s ∈ Icc a b, P s = Q s := by
  intro s hs
  have hPP := horizontalUnitAdapted_pair_eq hM12 hP hP ht₀ hs
  have hPQ := horizontalUnitAdapted_pair_eq hM12 hP hQ ht₀ hs
  have hQQ := horizontalUnitAdapted_pair_eq hM12 hQ hQ ht₀ hs
  rw [heq] at hPP hPQ
  by_contra hne
  have hpos := G.spacetime.horizontalMetric.pos (R.curve s) (P s - Q s)
    (sub_ne_zero.mpr hne)
  simp only [map_sub, sub_apply] at hpos
  rw [G.spacetime.horizontalMetric.symm (R.curve s) (Q s) (P s)] at hpos
  linarith

end PoincareMT.M14
