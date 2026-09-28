import PoincareConjecture.Proofs.M14.Sec6_3_GaugeVelocityPhase
import PoincareConjecture.Proofs.M14.Sec6_3_MaximalCoherence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point} {Z : G.Horizontal x}

theorem initialValueCurve_gauge_velocityPhase
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {S : ℝ} (hS : 0 < S) (hsurv : (Z, S) ∈ initialValueDomain G T x)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (x₀ : G.gaugeCover.spatial b) {a c : ℝ} (hac : a < c)
    (hsub : Icc a c ⊆ Icc 0 S)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
    (hrec : ∀ r ∈ Icc a c,
      (G.gaugeCover.cylinder b).toSpacetime (β r) = initialValueCurve G T x Z r)
    (hclock : ∀ r ∈ Icc a c, (β r).1.val = T - r ^ 2)
    {s : ℝ} (hs : s ∈ Ioo a c) :
    let q := fun r => (β r).2.val
    HasDerivAt (fun r => (q r, deriv q r))
      (Proofs.M09.regularizedCoordinatePhase
        (M08.chartActionMetric W.flow T x₀) (chartActionScalar W.flow T x₀)
        (s, (q s, deriv q s))) s := by
  obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hS).mp hsurv
  have hC : M14SqrtParameterInterval 0 (S ^ 2) = Icc 0 S := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hS.le]
  have hsub' : Icc a c ⊆ M14SqrtParameterInterval 0 (S ^ 2) := by
    rwa [hC]
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  exact squareRootEuler_gauge_velocityPhase P.square_path b hCoordinates hscalar W hM04 x₀
    hac hsub' hβ
    (fun r hr => (hrec r hr).trans (initialValueCurve_eqOn_square hM04 hM12 P (hsub' hr)))
    hclock P.extension hs (P.euler s (hsub' ⟨hs.1.le, hs.2.le⟩))

end PoincareConjecture.M14
