import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.OriginalCoefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LinearPostcompose




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter Poincare.Analysis.Calculus
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

theorem locally_eventually_contMDiff_originalNestedSpatialMap (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {σ : ℕ → ℕ}
    (hside : ∀ j, S.initialWindowIdentification P j ''
      closure ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
        (S.nestedWindowLimit P j).geometric_limit.exhaustion (σ j)) :
    ∀ x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier,
      ∃ V, IsOpen V ∧ x ∈ V ∧ ∀ᶠ j in atTop,
        ContMDiffOn (𝓡 n) (𝓡 n) ∞ (S.originalNestedSpatialMap P j (σ j)) V := by
  intro x
  obtain ⟨V, hV, hxV, hmaps⟩ := S.locally_eventually_contMDiff_nestedSpatialMap P hside x
  exact ⟨V, hV, hxV, hmaps.mono fun j hj =>
    (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm.contMDiff.comp_contMDiffOn hj⟩

set_option maxHeartbeats 800000 in
theorem tendstoUniformlyOn_originalNestedCoefficients_basis_jets (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {σ : ℕ → ℕ}
    (hside : ∀ j, S.initialWindowIdentification P j ''
      closure ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
        (S.nestedWindowLimit P j).geometric_limit.exhaustion (σ j))
    (q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier)
    (hjets : ∀ r : ℕ, ∀ A : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact A →
      A ⊆ Iio 0 ×ˢ (extChartAt (𝓡 n) q).target → TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ r (S.originalNestedCoefficients P q j (σ j)))
        (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.ancientWindowLimit P).flow.metric z.1).pullbackCoefficients
            (extChartAt (𝓡 n) q).symm z.2)) atTop A)
    (r : ℕ) (a b : Fin n) {A : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hAU : A ⊆ Iio 0 ×ˢ (extChartAt (𝓡 n) q).target) :
    TendstoUniformlyOn (fun j => iteratedFDeriv ℝ r (fun z =>
      S.originalNestedCoefficients P q j (σ j) z
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)))
      (iteratedFDeriv ℝ r ((S.ancientWindowLimit P).carrier.coordinateCoefficient q
        (fun t x v w => ((S.ancientWindowLimit P).flow.metric t).inner x v w) a b)) atTop A := by
  let L : (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ b)).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ a))
  have hlocal := RiemannianMetric.locally_eventually_smooth_spacetime_parametrized_coefficients
    isOpen_Iio
    (fun j => (S.rescaling ((S.nestedWindowLimit P j).geometric_limit.subsequence (σ j))).flow.smooth)
    (S.locally_eventually_contMDiff_originalNestedSpatialMap P hside)
    (isOpen_extChartAt_target (I := 𝓡 n) q) (contMDiffOn_extChartAt_symm (n := ∞) q)
  have hlimit : ContDiffOn ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      ((S.ancientWindowLimit P).flow.metric z.1).pullbackCoefficients
        (extChartAt (𝓡 n) q).symm z.2) (Iio 0 ×ˢ (extChartAt (𝓡 n) q).target) := by
    intro z hz
    exact ((S.ancientWindowLimit P).flow.smooth.contDiffAt_spacetime_pullbackCoefficients
      isOpen_Iio ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hz.2)) hz.1).contDiffWithinAt
  exact (smooth_convergence_continuousLinearMap_comp L
    (isOpen_Iio.prod (isOpen_extChartAt_target (I := 𝓡 n) q)) hlimit hlocal hjets).2 r A hA hAU

theorem nestedAncientEmbedding_coefficient_eq (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    (hstage : S.initialWindowIdentification P j ''
      ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
        (S.nestedWindowLimit P j).geometric_limit.exhaustion k)
    (q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier)
    (a b : Fin n) {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (hz : z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ (S.nestedWindowLimit P 0).geometric_limit.exhaustion j) :
    ancientPullbackCoefficient (S.nestedAncientEmbedding P j k hstage) q a b z =
      S.originalNestedCoefficients P q j k z
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b) := by
  let f := S.originalNestedSpatialMap P j k
  let c := (extChartAt (𝓡 n) q).symm
  have hf := (S.originalNestedSpatialMap_contMDiffAt P j k
    (hstage (mem_image_of_mem _ hz.2))).mdifferentiableAt (by simp)
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hz.1)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z.2 hf hc
  change ((S.rescaling ((S.nestedWindowLimit P j).geometric_limit.subsequence k)).flow.metric z.1).inner
    (f (c z.2))
    (mfderiv (𝓡 n) (𝓡 n) f (c z.2) (mfderiv (𝓡 n) (𝓡 n) c z.2 (EuclideanSpace.basisFun (Fin n) ℝ a)))
    (mfderiv (𝓡 n) (𝓡 n) f (c z.2) (mfderiv (𝓡 n) (𝓡 n) c z.2 (EuclideanSpace.basisFun (Fin n) ℝ b))) =
    ((S.rescaling ((S.nestedWindowLimit P j).geometric_limit.subsequence k)).flow.metric z.1).inner
      (f (c z.2))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c) z.2 (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c) z.2 (EuclideanSpace.basisFun (Fin n) ℝ b))
  rw [hd]
  rfl

end PoincareConjecture.AncientRescalingSequence
