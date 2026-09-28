import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.CompactControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.Convergence








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


def regularCoordinateDomain (H : SingularTimeAssumptions F T M) (q : M) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  (extChartAt (𝓡 3) q).target ∩
    (extChartAt (𝓡 3) q).symm ⁻¹' H.reference.regularLimitSet

theorem regularCoordinateDomain_isOpen (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (q : M) : IsOpen (H.regularCoordinateDomain q) :=
  (continuousOn_extChartAt_symm q).isOpen_inter_preimage (isOpen_extChartAt_target q)
    (H.regularLimitSet_isOpen P04)



theorem smooth_terminal_coordinate_limit_on_compacts
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) (q : M) :
    ContDiffOn ℝ ∞ (H.terminalCoordinateCoefficients P04 q) (H.regularCoordinateDomain q) ∧
      ∀ (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin 3))),
        IsCompact K → K ⊆ H.regularCoordinateDomain q →
        TendstoUniformlyOn
          (fun t => iteratedFDeriv ℝ m
            ((H.reference.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm))
          (iteratedFDeriv ℝ m (H.terminalCoordinateCoefficients P04 q)) (𝓝[<] T) K := by
  apply SingularRegularLimit.smooth_limit_of_eventual_jet_bounds
    (H.regularCoordinateDomain_isOpen P04 q)
  · exact fun z hz => H.tendsto_terminalCoordinateCoefficients P04 q hz.2
  · exact Eventually.of_forall fun t =>
      ((H.reference.flow.metric t).contDiffOn_chartCoefficients q).mono inter_subset_left
  · intro K hK hKU m
    have htarget : K ⊆ (extChartAt (𝓡 3) q).target := fun z hz => (hKU hz).1
    have hreg : (extChartAt (𝓡 3) q).symm '' K ⊆ H.reference.regularLimitSet := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hKU hz).2
    obtain ⟨s, _, hsT, hbound⟩ :=
      H.exists_uniform_coordinate_metric_jet_tail_on_compact P04 q hK htarget hreg
    obtain ⟨B, _, hB⟩ := hbound m
    refine ⟨B, ?_⟩
    filter_upwards [Ico_mem_nhdsLT hsT] with t ht
    exact hB t ht

end PoincareConjecture.SingularTimeAssumptions
