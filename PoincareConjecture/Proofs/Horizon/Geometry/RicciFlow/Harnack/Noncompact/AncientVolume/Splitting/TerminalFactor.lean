import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.Backward
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientFactor











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

open RiemannianMetric

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 1) M (Iic 0))
  (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
  (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
  {K : ℝ} (hK : 0 ≤ K)
  (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (hunit : HasUnitGradient (F.connection 0) f)
  (hzero : HasZeroHessian (F.connection 0) f)



def terminalParallelGradientFactor :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hunit x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hunit x) n 0
    RicciFlow n (zeroLevelSet f) (Iic 0) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hunit x) n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hunit x) n 0
  have hp := F.ancient_backward_persistence_of_parallel_gradient hC (by omega)
    hc hop ⟨K, hK, hbound⟩ f hf hunit hzero
  exact F.parallelGradientFactor hf (show (0 : ℝ) ∈ Iic 0 by simp)
    (fun t ht => (hp t ht).2.1) (fun t ht => (hp t ht).2.2)




theorem terminalParallelGradientFactor_ancient_geometry
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (hn : 0 < n) (p : M)
    (hscalar : 0 < (F.connection 0).scalarCurvature p)
    (hvolume : 0 < (F.metric 0).asymptoticVolumeRatio p) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hunit x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hunit x) n 0
    let H := F.terminalParallelGradientFactor hC hc hop hK hbound hf hunit hzero
    let κ := (F.metric 0).asymptoticVolumeRatio p / 2 ^ (n + 2)
    0 < κ ∧ Nonempty (zeroLevelSet f) ∧ ConnectedSpace (zeroLevelSet f) ∧
      NoncompactSpace (zeroLevelSet f) ∧
      (∀ t ≤ 0, MetricComplete (H.metric t)) ∧
      (∀ t ≤ 0, ∀ y, (H.connection t).NonnegativeCurvatureOperator y) ∧
      (∀ t ≤ 0, ∀ y, (H.connection t).curvatureTensorNorm y ≤ K) ∧
      (∃ y, 0 < (H.connection 0).scalarCurvature y ∧
        0 < (H.metric 0).asymptoticVolumeRatio y) ∧
      (∀ t ≤ 0, ∀ y, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (κ * r ^ n) ≤ (H.metric t).volumeMeasure ((H.metric t).ball y r)) ∧
      (∀ t ≤ 0, ∀ y, ∀ r : ℝ, 0 < r →
        (∀ s ∈ Icc (t - r ^ 2) t, ∀ z ∈ (H.metric t).ball y r,
          (H.connection s).curvatureTensorNorm z ≤ r⁻¹ ^ 2) →
        ENNReal.ofReal (κ * r ^ n) ≤ (H.metric t).volumeMeasure ((H.metric t).ball y r)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hunit x) n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hunit x) n 0
  have hp := F.ancient_backward_persistence_of_parallel_gradient hC (by omega)
    hc hop ⟨K, hK, hbound⟩ f hf hunit hzero
  exact F.parallelGradientFactor_ancient_geometry hn hC hc hop hK hbound hf
    (fun t ht => (hp t ht).2.1) (fun t ht => (hp t ht).2.2) p hscalar hvolume

end PoincareConjecture.RicciFlow
