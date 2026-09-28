import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Gluing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Parametrization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

noncomputable def nestedSpatialMap (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ) :
    (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier →
      (smallRescalingCarrier (n := n) (M := M)).carrier :=
  fun x => (((S.nestedWindowLimit P j).geometric_limit.embedding k).toFun
    (0, S.initialWindowIdentification P j x)).2

noncomputable def nestedSpatialCoefficients (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K)
    (q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier) (j k : ℕ) :
    ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  fun z => ((S.smallBasedWindow j ((S.nestedWindowLimit P j).geometric_limit.subsequence k)).metricAt
    z.1).pullbackCoefficients (S.nestedSpatialMap P j k ∘ (extChartAt (𝓡 n) q).symm) z.2

theorem identifiedWindowFlow_pullbackCoefficients (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ)
    (q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier)
    (t : ℝ) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q).target) :
    ((S.identifiedWindowFlow P j).metric t).pullbackCoefficients (extChartAt (𝓡 n) q).symm y =
      ((S.nestedWindowLimit P j).geometric_limit.limitFlow.metricAt t).pullbackCoefficients
        (S.initialWindowIdentification P j ∘ (extChartAt (𝓡 n) q).symm) y := by
  let e := S.initialWindowIdentification P j
  let c := (extChartAt (𝓡 n) q).symm
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c y :=
    (((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy))).mdifferentiableAt (by simp)
  have hd := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (c y)) hc
  ext v w
  change ((S.identifiedWindowFlow P j).metric t).inner (c y)
    (mfderiv (𝓡 n) (𝓡 n) c y v) (mfderiv (𝓡 n) (𝓡 n) c y w) =
      ((S.nestedWindowLimit P j).geometric_limit.limitFlow.metricAt t).inner (e (c y))
        (mfderiv (𝓡 n) (𝓡 n) (e ∘ c) y v) (mfderiv (𝓡 n) (𝓡 n) (e ∘ c) y w)
  rw [hd]
  rfl

theorem tendstoUniformlyOn_nestedSpatialCoefficients_jets (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ)
    (q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier) (r : ℕ)
    {A : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hAU : A ⊆ shiftedCompactnessWindow j ×ˢ (extChartAt (𝓡 n) q).target) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ r (S.nestedSpatialCoefficients P q j k))
      (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.gluedShiftedAncientFlow P).metric z.1).pullbackCoefficients
          (extChartAt (𝓡 n) q).symm z.2)) atTop A := by
  let G := (S.nestedWindowLimit P j).geometric_limit
  let e := S.initialWindowIdentification P j
  let c := (extChartAt (𝓡 n) q).symm
  have hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e ∘ c) (extChartAt (𝓡 n) q).target :=
    e.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm (n := ∞) q)
  have hj := G.tendstoUniformlyOn_parametrized_spacetime_jets
    (S.windowCompactnessHypotheses P j).time_bounds (isOpen_extChartAt_target (I := 𝓡 n) q)
    hf r hA hAU
  apply hj.congr_right
  have heq : EqOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (G.limitFlow.metricAt z.1).pullbackCoefficients (e ∘ c) z.2)
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.gluedShiftedAncientFlow P).metric z.1).pullbackCoefficients c z.2)
      (shiftedCompactnessWindow j ×ˢ (extChartAt (𝓡 n) q).target) := by
    intro z hz
    simp only [S.gluedShiftedAncientFlow_metric_eq P j hz.1]
    exact (S.identifiedWindowFlow_pullbackCoefficients P j q z.1 hz.2).symm
  exact (eqOn_iteratedFDeriv_of_isOpen
    (isOpen_Ioo.prod (isOpen_extChartAt_target (I := 𝓡 n) q)) heq r).mono hAU

end PoincareConjecture.AncientRescalingSequence
