import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-!
# Metric jets on the continuing interior

The singular-limit convergence stored in an old surgery event gives compact
uniform convergence to the actual post-surgery metric after retention. The
metric identity is differentiated only on the open continuing interior.
This is the spatial-jet input for smooth history gluing in Morgan--Tian,
Lemma 14.11 and Proposition 14.12, pp. 349-350.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- The metric-limit estimate is compact uniform convergence of each jet. -/
theorem SurgeryMetricLimitOn.tendstoUniformlyOn
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier} {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}
    (h : SurgeryMetricLimitOn A B g gT f U T)
    (q : A.carrier) (hq : q ∈ U) (K : Set (EuclideanSpace ℝ (Fin 3)))
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 3) q).target)
    (hKU : (extChartAt (𝓡 3) q).symm '' K ⊆ U)
    (k : ℕ) (a b : Fin 3) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k (singularMetricCoefficient (g t) q a b))
      (iteratedFDeriv ℝ k (surgeryMetricCoefficient gT
        (fun z => f ((extChartAt (𝓡 3) q).symm z)) a b)) (𝓝[<] T) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨d, hd, hbound⟩ := h q hq K hK hKt hKU k a b ε hε
  filter_upwards [Ioo_mem_nhdsLT (show T - d < T by linarith)] with t ht
  intro p hp
  simpa only [dist_eq_norm, norm_sub_rev] using hbound t ht.1 ht.2 p hp

/-- Translating the time coordinate preserves every spatial-jet limit. -/
theorem SurgeryMetricLimitOn.translateTime
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier} {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}
    (h : SurgeryMetricLimitOn A B g gT f U T) (s : ℝ) :
    SurgeryMetricLimitOn A B (fun t => g (t + s)) gT f U (T - s) := by
  intro q hq C hC hCt hCU k a b ε hε
  obtain ⟨d, hd, hbound⟩ := h q hq C hC hCt hCU k a b ε hε
  refine ⟨d, hd, ?_⟩
  intro t htd htT z hz
  exact hbound (t + s) (by linarith) (by linarith) z hz

namespace SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {S : ℝ → GeneralizedSliceCarrier.{u}}
  {g : ∀ t, RiemannianMetric 3 (S t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P S g T)

/-- The post-surgery and terminal-limit coefficient functions agree at each
point of the continuing interior, in an old slice chart. -/
theorem retained_metric_coefficient
    (q : (S E.tMinus).carrier) (a b : Fin 3)
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm z ∈ interior E.retained_pre) :
    surgeryMetricCoefficient (g T)
      (fun w => E.retention.map ((extChartAt (𝓡 3) q).symm w)) a b z =
    surgeryMetricCoefficient E.limit_metric
      (fun w => E.limit_identify.map ((extChartAt (𝓡 3) q).symm w)) a b z := by
  have hchart := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hz)).mdifferentiableAt (by simp)
  have hretained := (E.retention.map_smooth _ (interior_subset hret)).contMDiffAt
    (mem_interior_iff_mem_nhds.mp hret)
  have hregular := E.retained_pre_subset (interior_subset hret)
  have hlimit := (E.limit_identify.map_smooth _ hregular).contMDiffAt
    (E.regular_limit_open.mem_nhds hregular)
  change (g T).inner _
      (mfderiv (𝓡 3) (𝓡 3) (E.retention.map ∘ (extChartAt (𝓡 3) q).symm) z _)
      (mfderiv (𝓡 3) (𝓡 3) (E.retention.map ∘ (extChartAt (𝓡 3) q).symm) z _) =
    E.limit_metric.inner _
      (mfderiv (𝓡 3) (𝓡 3) (E.limit_identify.map ∘ (extChartAt (𝓡 3) q).symm) z _)
      (mfderiv (𝓡 3) (𝓡 3) (E.limit_identify.map ∘ (extChartAt (𝓡 3) q).symm) z _)
  rw [mfderiv_comp z (hretained.mdifferentiableAt (by simp)) hchart,
    mfderiv_comp z (hlimit.mdifferentiableAt (by simp)) hchart]
  exact E.retained_metric _ (interior_subset hret) _ _

/-- All spatial jets agree on the continuing interior. -/
theorem retained_metric_jets
    (q : (S E.tMinus).carrier) (k : ℕ) (a b : Fin 3)
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm z ∈ interior E.retained_pre) :
    iteratedFDeriv ℝ k (surgeryMetricCoefficient (g T)
      (fun w => E.retention.map ((extChartAt (𝓡 3) q).symm w)) a b) z =
    iteratedFDeriv ℝ k (surgeryMetricCoefficient E.limit_metric
      (fun w => E.limit_identify.map ((extChartAt (𝓡 3) q).symm w)) a b) z := by
  have hchart := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hz)
  have hnear :
      surgeryMetricCoefficient (g T)
          (fun w => E.retention.map ((extChartAt (𝓡 3) q).symm w)) a b =ᶠ[𝓝 z]
        surgeryMetricCoefficient E.limit_metric
          (fun w => E.limit_identify.map ((extChartAt (𝓡 3) q).symm w)) a b := by
    filter_upwards [(isOpen_extChartAt_target q).mem_nhds hz,
      hchart.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hret)] with w hw hwr
    exact E.retained_metric_coefficient q a b hw hwr
  exact (hnear.iteratedFDeriv ℝ k).self_of_nhds

/-- The actual pre-flow converges to the actual retained post-metric in every
spatial jet, uniformly on compact subsets of an old chart. -/
theorem tendstoUniformlyOn_retained_metric_jets
    (q : (S E.tMinus).carrier) (hq : q ∈ interior E.retained_pre)
    (C : Set (EuclideanSpace ℝ (Fin 3))) (hC : IsCompact C)
    (hCt : C ⊆ (extChartAt (𝓡 3) q).target)
    (hCr : (extChartAt (𝓡 3) q).symm '' C ⊆ interior E.retained_pre)
    (k : ℕ) (a b : Fin 3) :
    TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k (singularMetricCoefficient (E.pre_flow.metric t) q a b))
      (iteratedFDeriv ℝ k (surgeryMetricCoefficient (g T)
        (fun z => E.retention.map ((extChartAt (𝓡 3) q).symm z)) a b)) (𝓝[<] T) C := by
  have h := E.metric_converges.tendstoUniformlyOn q
    (E.retained_pre_subset (interior_subset hq)) C hC hCt
    (hCr.trans (interior_subset.trans E.retained_pre_subset)) k a b
  apply h.congr_right
  intro z hz
  exact (E.retained_metric_jets q k a b (hCt hz) (hCr (mem_image_of_mem _ hz))).symm

/-- Retention changes the terminal metric in the existing convergence statement
to the actual post-surgery metric, on the whole continuing interior. -/
theorem retained_metric_limit :
    SurgeryMetricLimitOn (S E.tMinus) (S T) E.pre_flow.metric (g T)
      E.retention.map (interior E.retained_pre) T := by
  intro q hq C hC hCt hCr k a b ε hε
  obtain ⟨d, hd, hbound⟩ := E.metric_converges q
    (E.retained_pre_subset (interior_subset hq)) C hC hCt
    (hCr.trans (interior_subset.trans E.retained_pre_subset)) k a b ε hε
  refine ⟨d, hd, ?_⟩
  intro t htd htT z hz
  rw [E.retained_metric_jets q k a b (hCt hz) (hCr (mem_image_of_mem _ hz))]
  exact hbound t htd htT z hz

end SurgeryEventData

end PoincareMT
