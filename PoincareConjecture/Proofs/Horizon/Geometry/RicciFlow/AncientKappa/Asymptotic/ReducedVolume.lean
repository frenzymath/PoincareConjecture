import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Asymptotic

set_option autoImplicit false

open Filter Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem ancientRescalingSequence_reducedVolume_limit
    {K : AncientKappaSolution n M} (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    ∃ V : ℝ, 0 ≤ V ∧ V < euclideanReducedVolume n ∧
      ∀ τ : ℝ, 0 < τ →
        Tendsto (fun k ↦ reducedVolume K.flow 0 S.reference (S.scale k * τ))
          atTop (𝓝 V) := by
  obtain ⟨A⟩ := P.structural
  have hscalar := (A.structural M K).scalar_pos (-1 / 2) (by norm_num) S.reference
  obtain ⟨V, hV0, hVE, _, hlim⟩ :=
    exists_ancient_reducedVolume_limit_lt_euclidean K.flow P.reduced_volume
      S.reference S.reference hscalar
  exact ⟨V, hV0, hVE, hlim S.scale S.scale_tendsto⟩

end PoincareConjecture
