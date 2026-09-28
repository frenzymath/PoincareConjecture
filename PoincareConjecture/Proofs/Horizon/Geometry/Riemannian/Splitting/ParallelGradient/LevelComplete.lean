import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.LevelSet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]



theorem zeroLevelMetric_complete
    (g : RiemannianMetric (n + 1) M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) (hc : MetricComplete g) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M) (fun x _ => hreg x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M) (fun x _ => hreg x) n 0
    MetricComplete (regularLevelMetric hf (⊤ : Opens M) (fun x _ => hreg x) 0 g) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf (⊤ : Opens M) (fun x _ => hreg x) n 0
  letI := isManifold_openLevelSet hf (⊤ : Opens M) (fun x _ => hreg x) n 0
  apply metricComplete_of_isClosedEmbedding
    (regularLevelMetric hf (⊤ : Opens M) (fun x _ => hreg x) 0 g) g
    (contMDiff_openLevelIncl hf (⊤ : Opens M) (fun x _ => hreg x) n 0)
    (F := zeroLevelIncl f)
  · refine ⟨isEmbedding_openLevelIncl f (⊤ : Opens M) 0, ?_⟩
    rw [zeroLevelRange]
    exact isClosed_singleton.preimage hf.continuous
  · exact regularLevelMetric_inner hf (⊤ : Opens M) (fun x _ => hreg x) 0 g
  · exact hc

end PoincareConjecture.RiemannianMetric
