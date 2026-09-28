import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenSubset
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion







open TopologicalSpace Function
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
  (c : ℝ)

local instance ambient_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩


def regularLevelMetric (g : RiemannianMetric (n + 1) M) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    RiemannianMetric n (openLevelSet f U c) := by
  letI := openLevelSetChartedSpace hf U hreg n c
  letI := isManifold_openLevelSet hf U hreg n c
  exact Induced.pullbackMetric g (openLevelIncl f U c)
    (contMDiff_openLevelIncl hf U hreg n c)
    (injective_mfderiv_openLevelIncl hf U hreg n c)

@[simp] theorem regularLevelMetric_inner (g : RiemannianMetric (n + 1) M)
    (x : openLevelSet f U c) (v w : EuclideanSpace ℝ (Fin n)) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    (regularLevelMetric hf U hreg c g).inner x v w =
      g.inner (openLevelIncl f U c x)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x v)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x w) := rfl


theorem regularLevelGeometry
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (g : RiemannianMetric (n + 1) M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (c : ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    ∃ gL : RiemannianMetric n (openLevelSet f U c),
      Topology.IsEmbedding (openLevelIncl f U c) ∧
      Set.range (openLevelIncl f U c) = (U : Set M) ∩ f ⁻¹' {c} ∧
      ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (openLevelIncl f U c) ∧
      (∀ x : openLevelSet f U c,
        Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x)) ∧
      (∀ x : openLevelSet f U c,
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).range =
        (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (openLevelIncl f U c x) :
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).ker) ∧
      (∀ (x : openLevelSet f U c) (v w : EuclideanSpace ℝ (Fin n)),
        gL.inner x v w = g.inner (openLevelIncl f U c x)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x v)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x w)) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf U hreg n c
  letI := isManifold_openLevelSet hf U hreg n c
  exact ⟨regularLevelMetric hf U hreg c g, isEmbedding_openLevelIncl f U c,
    range_openLevelIncl f U c, contMDiff_openLevelIncl hf U hreg n c,
    injective_mfderiv_openLevelIncl hf U hreg n c,
    range_mfderiv_openLevelIncl hf U hreg n c, regularLevelMetric_inner hf U hreg c g⟩

end PoincareConjecture.RiemannianMetric
