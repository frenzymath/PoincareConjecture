import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.LocalDiffeomorphism








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

noncomputable def smallShiftedAncientFlow (S : AncientRescalingSequence K) (k : ℕ) :
    RicciFlow n (smallRescalingCarrier (n := n) (M := M)).carrier (Iio 1) :=
  (S.rescaling k).flow.shrink.translate (-1)
    (by rintro t ⟨s, hs, rfl⟩; change s + -1 < 0; change s < 1 at hs; linarith)
    ordConnected_Iio ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩

theorem smallShiftedAncientFlow_metric (S : AncientRescalingSequence K) (j k : ℕ) (t : ℝ) :
    (S.smallShiftedAncientFlow k).metric t = (S.smallBasedWindow j k).metricAt t := rfl

noncomputable def nestedSpatialInverse (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ) :
    (smallRescalingCarrier (n := n) (M := M)).carrier →
      (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier :=
  fun y => (S.initialWindowIdentification P j).symm
    ((((S.nestedWindowLimit P j).geometric_limit.embedding k).inverse (0, y)).2)

theorem nestedSpatialMap_contMDiffAt (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    {x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier}
    (hx : S.initialWindowIdentification P j x ∈
      (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (S.nestedSpatialMap P j k) x := by
  exact (((S.nestedWindowLimit P j).geometric_limit.embedding k).spatialMap_contMDiffAt
    ((S.nestedWindowLimit P j).geometric_limit.exhaustion_open k)
    (S.windowCompactnessHypotheses P j).time_bounds hx).comp x
      (S.initialWindowIdentification P j).contMDiff.contMDiffAt

theorem nestedSpatialInverse_left (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    {x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier}
    (hx : S.initialWindowIdentification P j x ∈
      (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    S.nestedSpatialInverse P j k (S.nestedSpatialMap P j k x) = x := by
  let G := (S.nestedWindowLimit P j).geometric_limit
  let e := S.initialWindowIdentification P j
  have hpair : (G.embedding k).toFun (0, e x) = (0, S.nestedSpatialMap P j k x) :=
    Prod.ext ((G.embedding k).time_preserving 0 (e x)) rfl
  have hleft := congrArg Prod.snd
    ((G.embedding k).left_inverse (0, e x) ⟨(S.windowCompactnessHypotheses P j).time_bounds, hx⟩)
  rw [hpair] at hleft
  change e.symm (((G.embedding k).inverse (0, S.nestedSpatialMap P j k x)).2) = x
  rw [hleft, e.symm_apply_apply]

theorem nestedSpatialInverse_contMDiffAt (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    {x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier}
    (hx : S.initialWindowIdentification P j x ∈
      (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (S.nestedSpatialInverse P j k)
      (S.nestedSpatialMap P j k x) := by
  exact (S.initialWindowIdentification P j).symm.contMDiff.contMDiffAt.comp _
    (((S.nestedWindowLimit P j).geometric_limit.embedding k).spatialInverse_contMDiffAt
      ((S.nestedWindowLimit P j).geometric_limit.exhaustion_open k)
      (S.windowCompactnessHypotheses P j).time_bounds hx)

theorem nestedSpatialMap_base (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ) :
    S.nestedSpatialMap P j k (S.nestedWindowLimit P 0).geometric_limit.limitFlow.base =
      equivShrink M (S.base ((S.nestedWindowLimit P j).geometric_limit.subsequence k)) := by
  dsimp only [nestedSpatialMap]
  rw [S.initialWindowIdentification_base P j]
  exact congrArg Prod.snd ((S.nestedWindowLimit P j).geometric_limit.base_preserving k)

end PoincareConjecture.AncientRescalingSequence
