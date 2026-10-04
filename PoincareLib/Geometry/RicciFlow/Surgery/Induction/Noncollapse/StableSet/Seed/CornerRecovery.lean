import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Seed.CornerAction
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Gauge.GaugeRecoverySequence

/-!
# Admissible recovery of the actual seed comparison path

Morgan--Tian Claim 16.27, pp. 391-394. The minimizing prefix and
the seed-cylinder segment may have one corner. Actual inverse-gauge
recovery preserves their endpoints and clock and increases their
square action by an arbitrarily small amount.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareMT.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

/-- Recovering the one-corner comparison gives a literal admissible
backward path, with any prescribed positive action margin. -/
theorem oneCorner_admissible_recovery (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau c : ℝ} (htau : 0 < tau) (hc : c ∈ Icc 0 (Real.sqrt tau))
    (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (hleft : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma (Icc 0 c))
    (hright : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma (Icc c (Real.sqrt tau)))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ p : M14BackwardPath G T 0 tau (gamma 0) (gamma (Real.sqrt tau)),
      M14BackwardLAction G p <
        (∫ s in 0..Real.sqrt tau, M14.squareCurveDensity G gamma
          (Icc 0 (Real.sqrt tau)) s) + eta := by
  obtain ⟨R, hR⟩ := oneCorner_gauge_primitive_partition (Real.sqrt_pos.mpr htau)
    hc.1 hc.2 gamma hgamma hleft hright
  obtain ⟨_, haction⟩ := oneCorner_gauge_action_eq hM12 gamma hgamma hleft hright R hR
  obtain ⟨p, hp⟩ := gauge_primitive_recovery_sequence hM12 htau gamma hgamma hclock R
  have hlt : R.action < R.action + eta := lt_add_of_pos_right _ heta
  obtain ⟨k, hk⟩ := (hp.eventually_lt_const hlt).exists
  exact ⟨p k, haction ▸ hk⟩

end PoincareMT.Proofs.M46
