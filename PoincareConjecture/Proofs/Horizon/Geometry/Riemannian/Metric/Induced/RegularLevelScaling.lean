import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel

set_option autoImplicit false
open Set
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology
namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) M] [IsManifold (𝓡 (n+1)) ∞ M]
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ f)
  (U : TopologicalSpace.Opens M)
  (hreg : ∀ x∈U, mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) f x ≠ 0) (t : ℝ)
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
  ⟨finrank_euclideanSpace_fin⟩
theorem regularLevelMetric_rescaledMetric (g : RiemannianMetric (n+1) M)
    (c : ℝ) (hc : 0<c) :
    letI := openLevelSetChartedSpace hf U hreg n t
    letI := isManifold_openLevelSet hf U hreg n t
    (rescaledMetric g c hc).regularLevelMetric hf U hreg t =
      rescaledMetric (g.regularLevelMetric hf U hreg t) c hc := by
  rfl
theorem regularLevelMetric_rescaledMetric_edist (g : RiemannianMetric (n+1) M)
    (c : ℝ) (hc : 0<c) (x y : openLevelSet f U t) :
    letI := openLevelSetChartedSpace hf U hreg n t
    letI := isManifold_openLevelSet hf U hreg n t
    ((rescaledMetric g c hc).regularLevelMetric hf U hreg t).edist x y =
      ENNReal.ofReal (Real.sqrt c) * (g.regularLevelMetric hf U hreg t).edist x y := by
  let := openLevelSetChartedSpace hf U hreg n t
  let := isManifold_openLevelSet hf U hreg n t
  rw [regularLevelMetric_rescaledMetric]
  exact rescaledMetric_edist _ c hc x y
end PoincareConjecture.RiemannianMetric
