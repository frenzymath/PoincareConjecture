import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M45

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem model_metric_realization
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : E → M} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible) :
    ∃ (gE : RiemannianMetric 3 E) (_DE : LeviCivitaData gE) (W : Set E),
      IsOpen W ∧ (0 : E) ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, gE.euclideanCoefficients y = g.pullbackCoefficients f y := by
  apply RiemannianMetric.exists_local_realization hU hzero (g.pullbackCoefficients f)
  · exact fun y hy => (g.contDiffAt_pullbackCoefficients
      (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  · exact fun y _ v w => g.symm (f y) _ _
  · intro y hy v hv
    apply g.pos (f y)
    intro hz
    apply hv
    apply (hinv y hy).injective
    rw [map_zero]
    exact hz

end PoincareConjecture.M45
