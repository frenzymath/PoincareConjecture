import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Gluing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.CurvatureLimit








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem nestedWindowLimit_nonnegativeCurvatureOperator (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) (t : ℝ)
    (ht : t ∈ shiftedCompactnessWindow j) :
    ∀ x : (S.nestedWindowLimit P j).geometric_limit.limitCarrier.carrier,
      ((S.nestedWindowLimit P j).geometric_limit.limitFlow.flow.connection t).NonnegativeCurvatureOperator x := by
  apply (S.nestedWindowLimit P j).geometric_limit.nonnegativeCurvatureOperator_of_eventually t ht
  apply Eventually.of_forall
  intro k
  change ∀ x : (smallRescalingCarrier (n := n) (M := M)).carrier,
    ((S.rescaling k).flow.shrink.connection (t + -1)).NonnegativeCurvatureOperator x
  intro x
  rw [RicciFlow.shrink_nonnegativeCurvatureOperator_iff]
  exact (S.rescaling k).nonnegative_curvature_operator (t + -1)
    (by have := compactnessUpper_neg j; have := ht.2; change t < compactnessUpper j + 1 at this; linarith) _

theorem ancientWindowLimitFlow_nonnegativeCurvatureOperator (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (t : ℝ) (ht : t < 0)
    (x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier) :
    ((S.ancientWindowLimitFlow P).connection t).NonnegativeCurvatureOperator x := by
  let j := selectedCompactnessWindow (t + 1)
  change ((S.identifiedWindowFlow P j).connection (t + 1)).NonnegativeCurvatureOperator x
  rw [identifiedWindowFlow, RicciFlow.pullbackDiffeomorph_nonnegativeCurvatureOperator_iff]
  exact S.nestedWindowLimit_nonnegativeCurvatureOperator P j (t + 1)
    (selectedCompactnessWindow_mem (by linarith)) _

noncomputable def ancientWindowLimit (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) : AncientLimitFlow n where
  carrier := (S.nestedWindowLimit P 0).geometric_limit.limitCarrier
  base := (S.nestedWindowLimit P 0).geometric_limit.limitFlow.base
  flow := S.ancientWindowLimitFlow P
  complete := fun _ ht => S.ancientWindowLimitFlow_complete P ht
  nonnegative_curvature_operator := S.ancientWindowLimitFlow_nonnegativeCurvatureOperator P

end PoincareConjecture.AncientRescalingSequence
