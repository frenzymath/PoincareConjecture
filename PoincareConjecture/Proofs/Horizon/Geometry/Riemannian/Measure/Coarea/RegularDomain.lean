import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.LevelVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  (g : RiemannianMetric n M) {f : M → ℝ}
  (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)

def regularDomain : Opens M :=
  ⟨{x | 0 < g.tangentNorm x (g.gradient f x)},
    isOpen_lt continuous_const (g.continuous_tangentNorm_gradient hf)⟩

@[simp] theorem mem_regularDomain_iff (x : M) :
    x ∈ g.regularDomain hf ↔ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0 :=
  g.tangentNorm_gradient_pos_iff f x

theorem regularDomain_regular (x : M) (hx : x ∈ g.regularDomain hf) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0 :=
  (g.mem_regularDomain_iff hf x).mp hx

end PoincareConjecture.RiemannianMetric
