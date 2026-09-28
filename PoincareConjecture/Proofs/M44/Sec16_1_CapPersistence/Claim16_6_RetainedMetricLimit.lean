import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "basis" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}




theorem retained_surgeryMetricCoefficient
    (event : SurgeryEventData g0 K P slice metric T)
    {f : E → (slice event.tMinus).carrier} {x : E}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hx : f x ∈ interior event.retained_pre) (a b : Fin 3) :
    surgeryMetricCoefficient (metric T) (event.retention.map ∘ f) a b x =
      surgeryMetricCoefficient event.limit_metric (event.limit_identify.map ∘ f) a b x := by
  have hret := event.retention.map_smooth.contMDiffAt (mem_interior_iff_mem_nhds.mp hx)
  have hlim := event.limit_identify.map_smooth.contMDiffAt
    (event.regular_limit_open.mem_nhds (event.retained_pre_subset (interior_subset hx)))
  have hdret := mfderiv_comp x (hret.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  have hdlim := mfderiv_comp x (hlim.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  simpa only [surgeryMetricCoefficient, Function.comp_apply, hdret, hdlim,
    ContinuousLinearMap.comp_apply] using
      event.retained_metric (f x) (interior_subset hx)
        (mfderiv (𝓡 3) (𝓡 3) f x (basis a)) (mfderiv (𝓡 3) (𝓡 3) f x (basis b))




theorem retained_coefficient_germ
    (event : SurgeryEventData g0 K P slice metric T)
    (q : (slice event.tMinus).carrier) {x : E}
    (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm x ∈ interior event.retained_pre)
    (a b : Fin 3) :
    surgeryMetricCoefficient (metric T)
        (event.retention.map ∘ (extChartAt (𝓡 3) q).symm) a b =ᶠ[𝓝 x]
      surgeryMetricCoefficient event.limit_metric
        (event.limit_identify.map ∘ (extChartAt (𝓡 3) q).symm) a b := by
  have hc : ∀ y ∈ (extChartAt (𝓡 3) q).target,
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (extChartAt (𝓡 3) q).symm y := by
    intro y hy
    exact (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hy)
  have hnear := (hc x hx).continuousAt.preimage_mem_nhds
    (isOpen_interior.mem_nhds hret)
  filter_upwards [(isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hx, hnear] with y hy hyret
  exact retained_surgeryMetricCoefficient event (hc y hy) hyret a b





theorem metric_converges_retention
    (event : SurgeryEventData g0 K P slice metric T) :
    SurgeryMetricLimitOn (slice event.tMinus) (slice T) event.pre_flow.metric
      (metric T) event.retention.map (interior event.retained_pre) T := by
  intro q hq L hL hchart hret k a b eta heta
  have hregular : (extChartAt (𝓡 3) q).symm '' L ⊆ event.regular_limit :=
    hret.trans (interior_subset.trans event.retained_pre_subset)
  obtain ⟨d, hd, hbound⟩ := event.metric_converges q
    (event.retained_pre_subset (interior_subset hq)) L hL hchart hregular k a b eta heta
  refine ⟨d, hd, ?_⟩
  intro t ht hT x hx
  have hjet := ((retained_coefficient_germ event q (hchart hx)
    (hret (mem_image_of_mem _ hx)) a b).iteratedFDeriv ℝ k).self_of_nhds
  change iteratedFDeriv ℝ k (surgeryMetricCoefficient (metric T)
      (fun z => event.retention.map ((extChartAt (𝓡 3) q).symm z)) a b) x =
    iteratedFDeriv ℝ k (surgeryMetricCoefficient event.limit_metric
      (fun z => event.limit_identify.map ((extChartAt (𝓡 3) q).symm z)) a b) x at hjet
  rw [hjet]
  exact hbound t ht hT x hx

end PoincareConjecture.M44
