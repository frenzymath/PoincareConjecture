import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Metric.PullbackVariation.Soliton
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Slice


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
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





theorem negativeGradient_pullback_metric
    (L : AncientAsymptoticSolitonLimitData S)
    {Φ : ℝ → L.convergence.limit.carrier.carrier → L.convergence.limit.carrier.carrier}
    (hs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun z : ℝ × L.convergence.limit.carrier.carrier => Φ z.1 z.2) (Iio 0 ×ˢ univ))
    (hΦ : ∀ t < 0, ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3) (fun s => Φ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-((L.convergence.limit.flow.connection t).gradient
          (fun y => L.potential (y, t)) (Φ t x)))))
    (hinit : ∀ x, Φ (-1) x = x) {t : ℝ} (ht : t < 0)
    (x : L.convergence.limit.carrier.carrier) (v w : TangentSpace (𝓡 3) x) :
    (L.convergence.limit.flow.metric t).inner (Φ t x)
      (mfderiv (𝓡 3) (𝓡 3) (Φ t) x v) (mfderiv (𝓡 3) (𝓡 3) (Φ t) x w) =
        (-t) * (L.convergence.limit.flow.metric (-1)).inner x v w := by
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × L.convergence.limit.carrier.carrier => L.potential (z.2, z.1))
      (Iio 0 ×ˢ univ) :=
    L.potential_smooth.comp (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn
      (fun z hz => ⟨mem_univ z.2, hz.1⟩)
  have h := L.convergence.limit.flow.soliton_pullback_metric_eq_time_ratio
    isOpen_Iio hf hs hΦ (fun s hs => ne_of_lt hs) L.soliton_equation
    (s := -1) (by norm_num) ht x v w
  have hfun : Φ (-1) = id := funext hinit
  rw [hfun, mfderiv_id] at h
  simpa only [div_neg, div_one, id_eq, ContinuousLinearMap.id_apply] using h

end PoincareConjecture.AncientAsymptoticSolitonLimitData
