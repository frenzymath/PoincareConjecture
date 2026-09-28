import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.AsymptoticRoundness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Rigidity








set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem AncientAsymptoticSolitonLimitData.ancientRoundCertificate
    {K : AncientKappaSolution 2 M} {S : AncientRescalingSequence K}
    (L : AncientAsymptoticSolitonLimitData S) : TwoDimensionalAncientRoundCertificate K := by
  let C := L.convergence.limit.carrier
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
  let : CompactSpace M := L.convergence.compactSpace_of_compact_limit L.compactSpace
  have hR : ∀ x : C.carrier,
      (L.convergence.limit.flow.connection (-1)).scalarCurvature x = 1 := by
    simpa using L.scalar_eq_neg_inv_of_round (by norm_num : (-1 : ℝ) < 0)
      (L.round (by norm_num : (-1 : ℝ) < 0))
  have hlim := L.convergence.tendsto_scalarEntropy_rescaling L.compactSpace
    (by norm_num : (0 : ℝ) < 1) hR
  exact K.roundCertificate_of_backward_entropy_limit
    (tendsto_neg_atTop_atBot.comp
      (S.scale_tendsto.comp L.convergence.subsequence_strictMono.tendsto_atTop))
    (S.tendsto_scalarEntropy_original_of_rescaling L.convergence.subsequence hlim)

theorem TwoDimensionalClassificationPredecessors.ancientRoundCertificate_of_sequence
    (P : TwoDimensionalClassificationPredecessors (M := M))
    (K : AncientKappaSolution 2 M) (S : AncientRescalingSequence K) :
    TwoDimensionalAncientRoundCertificate K := by
  obtain ⟨L⟩ := P.m18 K S
  exact L.ancientRoundCertificate

end PoincareConjecture
