import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.StaticApproximation
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.FamilyApproximationFromStatic
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.DiskComparisonComplete
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.FiniteNetsComplete
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.FlowConclusionAssembly

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}

theorem m64FamilyApproximationTheory_of_M63
    (hM63 : M63RampEstimatesTheory.{u})
    (hcompact : IsCompact (Set.univ : Set M))
    (analytic : M63AnalyticConclusion F G) :
    M64FamilyApproximationTheory F G := by
  apply m64FamilyApproximationTheory_from_static_raw hM63 hcompact analytic
  intro Gamma hnull zeta hzeta
  exact (m64StaticApproximationTheory_of_compact (F.metric a) (F.connection a)
    hcompact).raw_family Gamma hnull zeta hzeta

theorem m64ThreeDimensionalFlowConclusion_of_flow_M63
    (hM63 : M63RampEstimatesTheory.{u})
    (hcompact : IsCompact (Set.univ : Set M))
    (flow : M64FlowConclusion F)
    (analytic : M63AnalyticConclusion F flow.geometry) :
    Nonempty (M64ThreeDimensionalFlowConclusion F) := by
  let approximation := m64FamilyApproximationTheory_of_M63 hM63 hcompact
    analytic
  let disks : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
      M64DiskAreaComparison (flow.geometry.product circumference h) t :=
    fun circumference h t ht => m64DiskAreaComparison_of_product
      (flow.geometry.product circumference h) t
  let finite_nets := m64FamilyAnnulusNets_of_compact flow.geometry hcompact
  exact m64ThreeDimensionalFlowConclusion_of_fields flow approximation disks finite_nets

end PoincareConjecture
