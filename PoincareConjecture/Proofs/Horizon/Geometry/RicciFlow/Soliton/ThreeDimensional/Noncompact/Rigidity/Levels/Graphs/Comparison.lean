import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graphs.Data
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.MetricExpansion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.LevelCurvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter Function
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S} {q : ℕ → M}
  {L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1}
  {B : G.NormalizedPotentialLimit L}
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
  [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {h : RiemannianMetric 2 N}
  {e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.limitCarrier.carrier}
  {base : N}

namespace PotentialLevelGraphs

variable (A : G.PotentialLevelGraphs L B h e base)

def center (k : ℕ) : M := q (L.subsequence (B.subsequence (k + A.offset)))

def level (k : ℕ) : ℝ := S.potential (A.center k)

theorem potential_map (k : ℕ) (y : N) : S.potential (A.map k y) = A.level k :=
  A.graph_level k y

def levelMap {a : ℝ}
    (hQ : ∀ x, a < S.potential x → 1 ≤ S.connection.levelQ S.potential x)
    (k : ℕ) (hk : a < A.level k) :
    N → openLevelSet S.potential (S.metric.regularDomain S.potential_contMDiff) (A.level k) :=
  fun y => ⟨⟨A.map k y, by
    change 0 < Real.sqrt (S.connection.levelQ S.potential (A.map k y))
    exact Real.sqrt_pos.mpr (zero_lt_one.trans_le (hQ _ (by rw [A.potential_map]; exact hk)))⟩,
    A.potential_map k y⟩

theorem levelMap_injective {a : ℝ}
    (hQ : ∀ x, a < S.potential x → 1 ≤ S.connection.levelQ S.potential x)
    (k : ℕ) (hk : a < A.level k) : Injective (A.levelMap hQ k hk) := by
  intro x y hxy
  apply A.graph_injective k
  exact congrArg (openLevelIncl S.potential
    (S.metric.regularDomain S.potential_contMDiff) (A.level k)) hxy

theorem scalarCurvature_lt_one
    (hD : S.connection.CurvatureTensorCalculus) {a : ℝ}
    (hQ : ∀ x, a < S.potential x → 1 < S.connection.levelQ S.potential x)
    (hR : ∀ x, a < S.potential x → S.connection.scalarCurvature x < 1)
    (k : ℕ) (hk : a < A.level k) (y : N) :
    (A.metric k).leviCivitaData.scalarCurvature y < 1 := by
  let U := S.metric.regularDomain S.potential_contMDiff
  let hreg := S.metric.regularDomain_regular S.potential_contMDiff
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace S.potential_contMDiff U hreg 2 (A.level k)
  let := isManifold_openLevelSet S.potential_contMDiff U hreg 2 (A.level k)
  let F := A.levelMap (fun x hx => (hQ x hx).le) k hk
  have heq := LeviCivitaData.scalarCurvature_eq_regularLevel_of_ambient_pullback
    S.potential_contMDiff U hreg (A.level k) S.metric (A.metric k)
    (A.metric k).leviCivitaData F (A.graph_contMDiff k) (A.metric_inner k) y
  rw [heq]
  apply S.regularLevel_scalarCurvature_lt_one_of_gradient_sq_gt_one hD U hreg (A.level k)
  · exact hR (A.map k y) (by rw [A.potential_map]; exact hk)
  · exact hQ (A.map k y) (by rw [A.potential_map]; exact hk)

variable [CompactSpace N] [ConnectedSpace N]

theorem area_le_of_center_flow {a : ℝ}
    (hQ : ∀ x, a < S.potential x → 1 ≤ S.connection.levelQ S.potential x)
    (hR : ∀ x, a < S.potential x → S.connection.scalarCurvature x ≤ 1)
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x)
      (S.connection.boundedNormalizedGradient S.potential))
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (Function.uncurry Φ))
    (hebase : e (base, 0) = L.base)
    (i j : ℕ) (hi : a < A.level i) (hij : A.level i ≤ A.level j)
    (hcenter : Φ (A.level j - A.level i) (A.center i) = A.center j) :
    (A.metric i).volumeMeasure.real univ ≤ (A.metric j).volumeMeasure.real univ := by
  let F := A.levelMap hQ i hi
  let F' := A.levelMap hQ j (hi.trans_le hij)
  have hbase : Φ (A.level j - A.level i)
      (openLevelIncl S.potential (S.metric.regularDomain S.potential_contMDiff)
        (A.level i) (F base)) =
      openLevelIncl S.potential (S.metric.regularDomain S.potential_contMDiff)
        (A.level j) (F' base) := by
    change Φ (A.level j - A.level i) (A.map i base) = A.map j base
    rw [A.map_base hebase, A.map_base hebase]
    exact hcenter
  obtain ⟨_, _, _, harea⟩ :=
    S.connection.exists_area_nondecreasing_diffeomorph_between_transported_levels
      S.potential_contMDiff hQ
      (fun x hx v _ => S.hessian_nonneg_of_scalarCurvature_le_one x (hR x hx) v)
      h0 hΦ hadd hs hi hij F F' (A.graph_contMDiff i) (A.graph_contMDiff j)
      (A.levelMap_injective hQ i hi) (A.levelMap_injective hQ j (hi.trans_le hij))
      (A.graph_immersion i) (A.graph_immersion j) (A.metric i) (A.metric j)
      (A.metric_inner i) (A.metric_inner j) base base hbase
  exact harea

theorem monotone_area_of_center_flow {a : ℝ}
    (hQ : ∀ x, a < S.potential x → 1 ≤ S.connection.levelQ S.potential x)
    (hR : ∀ x, a < S.potential x → S.connection.scalarCurvature x ≤ 1)
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x)
      (S.connection.boundedNormalizedGradient S.potential))
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (Function.uncurry Φ))
    (hebase : e (base, 0) = L.base) (hhigh : ∀ k, a < A.level k)
    (hlevel : Monotone A.level)
    (hcenter : ∀ i j, i ≤ j → Φ (A.level j - A.level i) (A.center i) = A.center j) :
    Monotone (fun k => (A.metric k).volumeMeasure.real univ) := by
  intro i j hij
  exact A.area_le_of_center_flow hQ hR h0 hΦ hadd hs hebase i j (hhigh i)
    (hlevel hij) (hcenter i j hij)

theorem area_le_limit_of_center_flow {a : ℝ}
    (hQ : ∀ x, a < S.potential x → 1 ≤ S.connection.levelQ S.potential x)
    (hR : ∀ x, a < S.potential x → S.connection.scalarCurvature x ≤ 1)
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x)
      (S.connection.boundedNormalizedGradient S.potential))
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (Function.uncurry Φ))
    (hebase : e (base, 0) = L.base) (hhigh : ∀ k, a < A.level k)
    (hlevel : Monotone A.level)
    (hcenter : ∀ i j, i ≤ j → Φ (A.level j - A.level i) (A.center i) = A.center j)
    (k : ℕ) : (A.metric k).volumeMeasure.real univ ≤ h.volumeMeasure.real univ :=
  Monotone.ge_of_tendsto
    (A.monotone_area_of_center_flow hQ hR h0 hΦ hadd hs hebase hhigh hlevel hcenter)
    A.area_tendsto k

end PotentialLevelGraphs

end PoincareConjecture.ShrinkingSolitonFlow
