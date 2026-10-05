import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Gluing.OpenMetricJets
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.History.OpenFlow

/-!
# The terminal metric limit on the continuing carrier

Both sides of an old surgery are expressed on the continuing pre-interior.
The stored singular-limit convergence is transported to the post-flow's
initial metric, without changing the retention map or adding a gluing premise.
Source: Morgan--Tian, Lemma 14.11 and Proposition 14.12, pp. 349-350.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- Pulling the target metric back replaces its map by the identity in the
actual metric-jet convergence statement. -/
theorem SurgeryMetricLimitOn.pullbackTarget
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier} {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}
    (h : SurgeryMetricLimitOn A B g gT f U T)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) :
    SurgeryMetricLimitOn A A g (gT.pullbackOfLocalDiffeomorph f hf) id U T := by
  intro q hq C hC hCt hCU k a b ε hε
  obtain ⟨d, hd, hbound⟩ := h q hq C hC hCt hCU k a b ε hε
  refine ⟨d, hd, ?_⟩
  intro t htd htT z hz
  have hnear :
      surgeryMetricCoefficient (gT.pullbackOfLocalDiffeomorph f hf)
          (fun w => id ((extChartAt (𝓡 3) q).symm w)) a b =ᶠ[𝓝 z]
        surgeryMetricCoefficient gT (fun w => f ((extChartAt (𝓡 3) q).symm w)) a b := by
    filter_upwards [(isOpen_extChartAt_target q).mem_nhds (hCt hz)] with w hw
    have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hw)).mdifferentiableAt (by simp)
    have hfc := mfderiv_comp w
      ((hf.contMDiff _).mdifferentiableAt (by simp)) hc
    change gT.inner (f ((extChartAt (𝓡 3) q).symm w))
        (mfderiv (𝓡 3) (𝓡 3) f _
          (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm w _))
        (mfderiv (𝓡 3) (𝓡 3) f _
          (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm w _)) =
      gT.inner (f ((extChartAt (𝓡 3) q).symm w))
        (mfderiv (𝓡 3) (𝓡 3) (f ∘ (extChartAt (𝓡 3) q).symm) w _)
        (mfderiv (𝓡 3) (𝓡 3) (f ∘ (extChartAt (𝓡 3) q).symm) w _)
    rw [hfc]
    rfl
  rw [(hnear.iteratedFDeriv ℝ k).self_of_nhds]
  exact hbound t htd htT z hz

namespace SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {S : ℝ → GeneralizedSliceCarrier.{u}}
  {g : ∀ t, RiemannianMetric 3 (S t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P S g T)

/-- The two constructed continuing flows have the exact full-domain metric
limit required for smooth time gluing on their common carrier. -/
theorem continuing_metric_limit {J : Set ℝ} (F : RicciFlow 3 (S T).carrier J)
    (hF : F.metric T = g T) :
    SurgeryMetricLimitOn
      ((S E.tMinus).openSubset (SurgeryRegionEquivalence.sourceInterior (U := E.retained_pre)))
      ((S E.tMinus).openSubset (SurgeryRegionEquivalence.sourceInterior (U := E.retained_pre)))
      E.continuingPreFlow.metric ((E.continuingPostFlow F).metric T) id univ T := by
  simp only [continuingPreFlow, continuingPostFlow,
    GeneralizedSliceCarrier.openSubsetFlow, SurgeryRegionEquivalence.pullbackInteriorFlow,
    RicciFlow.restrictToOpen, RicciFlow.pullbackWithConnection, hF]
  let V := SurgeryRegionEquivalence.sourceInterior (U := E.retained_pre)
  let C := (S E.tMinus).openSubset V
  have h₀ : SurgeryMetricLimitOn C (S T)
      (fun t => (S E.tMinus).openSubsetMetric V (E.pre_flow.metric t))
      (g T) E.retention.interiorMap univ T :=
    E.retained_metric_limit.openSubset V subset_rfl
  have h := SurgeryMetricLimitOn.pullbackTarget (A := C) (B := S T) h₀
    E.retention.interiorMap_isLocalDiffeomorph
  exact h

end SurgeryEventData

end PoincareMT
