import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.FullDomainScalarNormalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.CenteredError
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainFamilyComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

open MetricSurgery

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem eventually_scalarNormalized_neck_familyClose
    (F : RicciFlow 3 M (Iic 0)) (N : EpsilonNeck (F.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {r : ℝ} (hr : 0 < r)
    (hclose : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => r * roundCylinderPullback (F.metric (u / r))
        N.coordinate_map z v w))
    {κ : Type*} {l : Filter κ} {s : κ → ℝ} (hs : Tendsto s l (𝓝 r)) :
    ∀ᶠ k in l, RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => s k * roundCylinderPullback (F.metric (u / s k))
        N.coordinate_map z v w) := by
  apply TerminalNeck.eventually_roundCylinderFamilyClose_of_centeredDifferenceJets_fullDomain
    N.epsilon_pos hclose
  · filter_upwards [] with k u _
    exact roundCylinderTensorSmoothOn_smul_pullback (F.metric (u / s k))
      N.coordinate_map_smooth (s k)
  · intro eta heta
    filter_upwards [F.eventually_scalarNormalized_centeredNeck_jets_full_domain_uniform_time
      N hcompact hsmall hr hs heta] with k hk u hu z hz j hj
    rw [centeredCylinderError_difference_jet_eq
      (F.metric (u / s k)) (F.metric (u / r)) N.coordinate_map N.coordinate_map
      (s k) r z.1 z.2 (isOpen_univ.prod isOpen_Ioo) ⟨mem_univ _, hz⟩
      N.coordinate_map_smooth N.coordinate_map_smooth j]
    exact hk u ⟨hu.1.le, hu.2⟩ z hz j hj

end PoincareConjecture.RicciFlow
