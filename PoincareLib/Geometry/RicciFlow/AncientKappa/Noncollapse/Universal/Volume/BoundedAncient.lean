import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.Compact
import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.PastControl
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ZeroVolume.Theorem

/-!
# Applying bounded ancient volume decay to ancient kappa-solutions

This adapter combines compact-volume decay with the bounded-ancient
noncompact theorem, and identifies its real normalized-volume limit with
the exact calibrated infimum used by ancient kappa-solutions.

Reference: Morgan--Tian, Theorem 9.59, pp. 222--225; Kleiner--Lott
(corrected 2013), Proposition 41.13, p. 2678.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.AncientKappaSolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- The bounded-ancient volume theorem applies after differential Harnack
upgrades the per-slice bound to one bound on the whole ancient interval.
Only the analytic curvature services are used by the reused theorem. -/
theorem asymptotic_volume_ratio_zero_of_curvature_and_differential
    (K : AncientKappaSolution n M) (hC : RicciFlowCurvatureCalculus.{u})
    (hdifferential : ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x) dR
          (Iic 0) t ∧
        dR + 2 * (mvfderiv (𝓡 n)
          (fun y => (K.flow.connection t).scalarCurvature y) x) v +
          2 * (K.flow.connection t).ricci x v v ≥ 0) :
    AncientAsymptoticVolumeRatioZero K := by
  classical
  have hcalculus (t : ℝ) (_ht : t ≤ 0) :
      (K.flow.connection t).CurvatureTensorCalculus :=
    hC.tensor_calculus n M (K.flow.metric t) (K.flow.connection t)
  by_cases hcompact : CompactSpace M
  · letI : CompactSpace M := hcompact
    exact K.asymptotic_volume_ratio_zero_of_compact (hcalculus 0 le_rfl)
  · letI : NoncompactSpace M := not_compactSpace_iff.mp hcompact
    obtain ⟨C, hCnonneg, hbound⟩ := K.whole_past_bound_of_scalar_monotone hcalculus
      (K.scalar_monotone_of_differential hdifferential)
    have hdecay := RicciFlow.zero_asymptoticVolumeRatio_of_bounded_ancient
      (K.two_le_dimension (hcalculus 0 le_rfl)) hC K.flow K.complete
      K.nonnegative_curvature_operator hCnonneg hbound K.kappa_pos
      K.closed_cylinder_volume_lower_bound
      (K.exists_scalar_pos_of_tensor_calculus 0 le_rfl (hcalculus 0 le_rfl))
    intro t ht p
    exact (K.flow.metric t).calibrated_asymptoticVolumeRatio_eq_zero_of_tendsto p
      (fun r _ => ((K.flow.metric t).volumeMeasure_ball_lt_top (K.complete t ht) p r).ne)
      (hdecay t ht p).2

end PoincareMT.AncientKappaSolution
