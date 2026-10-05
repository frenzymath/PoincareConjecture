import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Transport.AnalyticBounds
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.BackwardStable

/-!
# Full-carrier monotonicity from the analytic witnesses

The fixed-source monotonicity field compares the later carrier with
its image at an earlier time. Nonnegative density then enlarges to the
whole earlier stable carrier. An empty terminal carrier has zero volume.
Morgan-Tian Theorem 6.80 and Proposition 6.81, pp. 144-146.
-/

set_option autoImplicit false

open Set MeasureTheory

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- Analytic witnesses at all positive stable times give the frozen
full reduced-volume monotonicity statement, including an empty
terminal carrier, Theorem 6.80, pp. 144-146. -/
theorem reducedVolumeStatement_of_analytic
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hanalytic : ∀ (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
      (H : M14StableSet G T τ x E), Nonempty (M14ReducedVolumeAnalyticData G T τ x E H)) :
    M14ReducedVolumeStatement G := by
  intro T x E τmax _ Hmax τ hτ hle
  obtain ⟨Amax⟩ := hanalytic T τmax x E Hmax
  by_cases hne : Hmax.carrier.Nonempty
  · have hmin : ∀ Z ∈ Hmax.carrier,
        ∃ p : M14BackwardPath G T 0 τmax x (Hmax.endpoint_map Z), M14IsMinimizing p := by
      intro Z hZ
      obtain ⟨p, _, hp, _⟩ := Hmax.minimizing_path Z hZ
      exact ⟨p, hp⟩
    obtain ⟨Hτ, hsub, hmono⟩ := Amax.fixed_W_monotone Hmax.carrier Subset.rfl hne
      Hmax.carrier_open Hmax.carrier_open.measurableSet hmin τ hτ hle
    obtain ⟨Aτ⟩ := hanalytic T τ x E Hτ
    refine ⟨Hτ, hsub, ?_⟩
    rw [← analyticCarrier_eq_stableVolume Hmax Amax,
      ← analyticCarrier_eq_stableVolume Hτ Aτ]
    have hcompare : M14ReducedVolumeOnAnalyticCarrier Amax Hmax.carrier ≤
        M14ReducedVolumeOnAnalyticCarrier Aτ Hmax.carrier := by
      rw [analyticCarrier_eq_densityIntegral Hτ Aτ hsub Hmax.carrier_open.measurableSet]
      exact hmono
    exact hcompare.trans (analyticCarrier_mono Hτ Aτ hsub Subset.rfl
      Hτ.carrier_open.measurableSet)
  · obtain ⟨Hτ, hsub⟩ := exists_stableSet_backward hCoordinates hM04 hM12 E Hmax hτ hle
    obtain ⟨Aτ⟩ := hanalytic T τ x E Hτ
    refine ⟨Hτ, hsub, ?_⟩
    have hempty : Hmax.carrier = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [← analyticCarrier_eq_stableVolume Hmax Amax,
      ← analyticCarrier_eq_stableVolume Hτ Aτ]
    have hzero : M14ReducedVolumeOnAnalyticCarrier Amax Hmax.carrier = 0 := by
      simp [M14ReducedVolumeOnAnalyticCarrier, hempty]
    rw [hzero]
    exact analyticCarrier_nonneg Hτ Aτ Subset.rfl Hτ.carrier_open.measurableSet

end PoincareMT.M14
