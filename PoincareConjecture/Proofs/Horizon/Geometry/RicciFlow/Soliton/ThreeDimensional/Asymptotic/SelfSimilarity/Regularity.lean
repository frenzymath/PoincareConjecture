import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Slice

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem contMDiffOn_negative_potential_gradient (L : AncientAsymptoticSolitonLimitData S) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × L.convergence.limit.carrier.carrier =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin 3)) p.2
          (-((L.convergence.limit.flow.connection p.1).gradient
            (fun y => L.potential (y, p.1)) p.2))) (Iio 0 ×ˢ univ) := by
  rintro ⟨t, x⟩ ⟨ht, _⟩
  have hf := L.potential_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Iio).mem_nhds (show (x, t) ∈ univ ×ˢ Iio 0 from ⟨mem_univ _, ht⟩))
  exact (L.convergence.limit.flow.contMDiffAt_negative_gradient
    (by simpa only [interior_Iio] using ht)
    (hf.comp (t, x) (contMDiffAt_snd.prodMk contMDiffAt_fst))).contMDiffWithinAt

end PoincareConjecture.AncientAsymptoticSolitonLimitData
