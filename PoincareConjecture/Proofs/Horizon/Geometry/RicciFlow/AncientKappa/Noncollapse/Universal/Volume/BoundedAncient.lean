import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.PastControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ZeroVolume.Theorem

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

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
      (K.two_le_dimension (hcalculus 0 le_rfl)) ricciFlowCurvatureTheory K.flow K.complete
      K.nonnegative_curvature_operator hCnonneg hbound K.kappa_pos
      K.closed_cylinder_volume_lower_bound
      (K.exists_scalar_pos_of_tensor_calculus 0 le_rfl (hcalculus 0 le_rfl))
    intro t ht p
    exact (K.flow.metric t).calibrated_asymptoticVolumeRatio_eq_zero_of_tendsto p
      (fun r _ => ((K.flow.metric t).volumeMeasure_ball_lt_top (K.complete t ht) p r).ne)
      (hdecay t ht p).2

end PoincareConjecture.AncientKappaSolution
