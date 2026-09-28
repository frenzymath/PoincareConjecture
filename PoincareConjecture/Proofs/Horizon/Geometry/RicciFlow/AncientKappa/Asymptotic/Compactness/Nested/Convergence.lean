import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Diagonal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.SourceGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Atlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem locally_eventually_contMDiff_nestedSpatialMap (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {σ : ℕ → ℕ}
    (hside : ∀ j, S.initialWindowIdentification P j ''
      closure ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
        (S.nestedWindowLimit P j).geometric_limit.exhaustion (σ j)) :
    ∀ x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier,
      ∃ V, IsOpen V ∧ x ∈ V ∧ ∀ᶠ j in atTop,
        ContMDiffOn (𝓡 n) (𝓡 n) ∞ (S.nestedSpatialMap P j (σ j)) V := by
  intro x
  obtain ⟨s, hs⟩ := (S.nestedWindowLimit P 0).geometric_limit.exists_exhaustion_superset
    (isCompact_singleton (x := x))
  refine ⟨(S.nestedWindowLimit P 0).geometric_limit.exhaustion s,
    (S.nestedWindowLimit P 0).geometric_limit.exhaustion_open s, hs (mem_singleton x), ?_⟩
  filter_upwards [eventually_ge_atTop s] with j hj y hy
  exact (S.nestedSpatialMap_contMDiffAt P j (σ j)
    (hside j (mem_image_of_mem _ (subset_closure
      ((S.nestedWindowLimit P 0).geometric_limit.exhaustion_monotone hj hy))))).contMDiffWithinAt

theorem exists_nested_spatial_diagonal_all_charts (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ j, S.initialWindowIdentification P j ''
        closure ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
          (S.nestedWindowLimit P j).geometric_limit.exhaustion (σ j)) ∧
      ∀ q : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier, ∀ r : ℕ,
      ∀ A : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact A →
      A ⊆ Iio 1 ×ˢ (extChartAt (𝓡 n) q).target →
        TendstoUniformlyOn
          (fun j => iteratedFDeriv ℝ r (S.nestedSpatialCoefficients P q j (σ j)))
          (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((S.gluedShiftedAncientFlow P).metric z.1).pullbackCoefficients
              (extChartAt (𝓡 n) q).symm z.2)) atTop A := by
  let T := (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.compactChartTests
  obtain ⟨σ, hσ, hside, htests⟩ := S.exists_nested_spatial_diagonal P T
  refine ⟨σ, hσ, hside, fun q r A hA hAU => ?_⟩
  have hchosen (i r : ℕ) (A : Set (ℝ × EuclideanSpace ℝ (Fin n)))
      (hA : IsCompact A) (hAU : A ⊆ Iio 1 ×ˢ (extChartAt (𝓡 n) (T.center i)).target) :
      TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ r (S.nestedSpatialCoefficients P (T.center i) j (σ j)))
        (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.gluedShiftedAncientFlow P).metric z.1).pullbackCoefficients
            (extChartAt (𝓡 n) (T.center i)).symm z.2)) atTop A := by
    obtain ⟨m, hm⟩ := T.cofinal i A hA hAU
    exact (htests i m r).mono hm
  exact RiemannianMetric.tendstoUniformlyOn_parametrized_jets_of_chart_cover T.center T.covers
    isOpen_Iio
    (fun j => (S.smallShiftedAncientFlow
      ((S.nestedWindowLimit P j).geometric_limit.subsequence (σ j))).smooth)
    (S.gluedShiftedAncientFlow P).smooth
    (S.locally_eventually_contMDiff_nestedSpatialMap P hside) hchosen
    (isOpen_extChartAt_target (I := 𝓡 n) q) (contMDiffOn_extChartAt_symm (n := ∞) q) r hA hAU

end PoincareConjecture.AncientRescalingSequence
