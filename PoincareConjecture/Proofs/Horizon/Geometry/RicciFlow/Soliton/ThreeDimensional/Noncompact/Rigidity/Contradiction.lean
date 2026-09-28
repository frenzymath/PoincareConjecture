import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graphs
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graphs.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Contradiction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.ScalarUpper
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Transport.Escape
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.NullReduction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Set Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GradientShrinkingSolitonData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem not_ricci_positive_of_noncompact
    (S : GradientShrinkingSolitonData 3 M)
    (hP : ThreeDimensionalClassificationPredecessors.{u}) (hM : ¬ CompactSpace M) :
    ¬ ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < S.connection.ricci x v v := by
  intro hRic
  have hD := hP.curvature.tensor_calculus 3 M S.metric S.connection
  obtain ⟨a₀, ha₀⟩ := S.exists_gradient_sq_gt_on_superlevel hD 1
  obtain ⟨a₁, ha₁⟩ := S.exists_threshold_scalarCurvature_lt_one hP hRic
  let a := max a₀ a₁
  have hQ (y : M) (hy : a < S.potential y) :
      1 < S.connection.levelQ S.potential y :=
    ha₀ y ((le_max_left _ _).trans hy.le)
  have hR (y : M) (hy : a < S.potential y) :
      S.connection.scalarCurvature y < 1 :=
    ha₁ y ((le_max_right _ _).trans hy.le)
  have hQle := fun y hy => (hQ y hy).le
  obtain ⟨x, hx⟩ := S.exists_potential_gt_of_noncompact hM a
  obtain ⟨Φ, h0, hΦ, hadd, hs⟩ :=
    S.connection.exists_complete_boundedNormalizedGradient_flow S.complete S.potential_contMDiff
  let q : ℕ → M := fun k => Φ (k : ℝ) x
  have hstart : a < S.potential (Φ 0 x) := by rwa [h0]
  have hescape := S.normalizedGradient_curve_centers_escape hQle (hΦ x) hstart x
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  obtain ⟨L, hc⟩ := G.exists_unscaledPointedLimit hP.curvature q
  obtain ⟨B⟩ := G.exists_normalizedPotentialLimit L hD x hescape hc
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun y (_ : y ∈ (⊤ : Opens L.limitCarrier.carrier)) =>
    RiemannianMetric.regular_of_hasUnitGradient B.unitGradient y
  let := openLevelSetChartedSpace B.potential_contMDiff
    (⊤ : Opens L.limitCarrier.carrier) hreg 2 0
  let := isManifold_openLevelSet B.potential_contMDiff
    (⊤ : Opens L.limitCarrier.carrier) hreg 2 0
  let N := RiemannianMetric.zeroLevelSet B.potential
  let h := RiemannianMetric.regularLevelMetric B.potential_contMDiff
    (⊤ : Opens L.limitCarrier.carrier) hreg 0 (L.limitFlow.metric 0)
  obtain ⟨hconn, hcompact, _, hunit, e, _, _, hebase, ⟨A⟩⟩ :=
    G.exists_zeroLevel_potentialLevelGraphs L B hP hD x hescape hc
  let : ConnectedSpace N := hconn
  let : CompactSpace N := hcompact
  have hlevel (k : ℕ) : A.level k = S.potential x +
      (L.subsequence (B.subsequence (k + A.offset)) : ℝ) :=
    S.potential_normalizedGradient_flow_nat hQle h0 hΦ hx _
  have hhigh (k : ℕ) : a < A.level k := by
    rw [hlevel]
    exact hx.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hmono : Monotone A.level := by
    intro i j hij
    rw [hlevel, hlevel]
    have hij' : L.subsequence (B.subsequence (i + A.offset)) ≤
        L.subsequence (B.subsequence (j + A.offset)) :=
      L.subsequence_strictMono.monotone
        (B.subsequence_strictMono.monotone (Nat.add_le_add_right hij _))
    apply add_le_add le_rfl
    exact_mod_cast hij'
  have hcenter (i j : ℕ) (_hij : i ≤ j) :
      Φ (A.level j - A.level i) (A.center i) = A.center j :=
    S.normalizedGradient_flow_between_centers hQle h0 hΦ hadd hx _ _
  have harea := A.monotone_area_of_center_flow hQle (fun y hy => (hR y hy).le)
    h0 hΦ hadd hs hebase hhigh hmono hcenter
  exact h.false_of_subunit_scalar_nondecreasing_area_limit A.metric hunit
    (A.scalarCurvature_lt_one hD hQ hR 0 (hhigh 0))
    (fun k => harea (Nat.zero_le k)) A.area_tendsto

theorem exists_null_plane_of_noncompact
    (S : GradientShrinkingSolitonData 3 M)
    (hP : ThreeDimensionalClassificationPredecessors.{u}) (hM : ¬ CompactSpace M) :
    ∃ (x : M) (v w : TangentSpace (𝓡 3) x),
      S.metric.inner x v v = 1 ∧ S.metric.inner x w w = 1 ∧
      S.metric.inner x v w = 0 ∧ S.connection.curvatureTensor x v w v w = 0 :=
  S.connection.exists_null_plane_of_not_ricci_positive
    (hP.curvature.tensor_calculus 3 M S.metric S.connection)
    S.nonnegative_curvature (S.not_ricci_positive_of_noncompact hP hM)

end PoincareConjecture.GradientShrinkingSolitonData
