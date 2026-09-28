import PoincareConjecture.Proofs.M34.Standard.FlowJoiningCoefficients
import PoincareConjecture.Proofs.M34.Standard.FlowLocality
import PoincareConjecture.Proofs.M34.Standard.RicciOperatorEvaluation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Coordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.FlowJoining

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {S τ : ℝ}
  (G : RicciFlow 3 StandardCapSpace (Icc 0 S))
  (H : RicciFlow 3 StandardCapSpace (Ico 0 τ))




noncomputable def metricConnection (t : ℝ) :
    Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g :=
  if t < S then ⟨G.metric t, G.connection t⟩
  else ⟨H.metric (t - S), H.connection (t - S)⟩


noncomputable def metric (t : ℝ) : RiemannianMetric 3 StandardCapSpace :=
  (metricConnection G H t).1



noncomputable def connection (t : ℝ) : LeviCivitaData (metric G H t) :=
  (metricConnection G H t).2



theorem metricConnection_of_lt {t : ℝ} (ht : t < S) :
    metricConnection G H t = ⟨G.metric t, G.connection t⟩ := by
  simp only [metricConnection, ht, if_true]



theorem metric_of_lt {t : ℝ} (ht : t < S) : metric G H t = G.metric t := by
  simp only [metric, metricConnection_of_lt G H ht]



theorem connection_of_lt {t : ℝ} (ht : t < S) :
    HEq (connection G H t) (G.connection t) :=
  (Sigma.mk.inj_iff.mp (metricConnection_of_lt G H ht)).2



theorem metric_of_le {t : ℝ} (ht : S ≤ t) : metric G H t = H.metric (t - S) := by
  simp only [metric, metricConnection, not_lt.mpr ht, if_false]




theorem metric_coefficients (t : ℝ) :
    (metric G H t).euclideanCoefficients = fun x => coefficients G H (t, x) := by
  by_cases ht : t < S
  · simp only [metric_of_lt G H ht, coefficients_of_lt G H ht]
  · simp only [metric_of_le G H (not_lt.mp ht), coefficients_of_le G H (not_lt.mp ht)]

variable (hS : 0 < S) (hτ : 0 < τ) (hinit : H.metric 0 = G.metric S)

include hS hτ hinit



theorem coefficients_smooth :
    ContDiffOn ℝ ∞ (coefficients G H) (Ico 0 (S + τ) ×ˢ univ) := by
  intro p hp
  by_cases ht : p.1 < S
  · have hnear : {q : ℝ × StandardCapSpace | q.1 < S} ∈
        𝓝[Ico 0 (S + τ) ×ˢ univ] p :=
      mem_nhdsWithin_of_mem_nhds ((isOpen_Iio.preimage continuous_fst).mem_nhds ht)
    have hdom : Icc 0 S ×ˢ (univ : Set StandardCapSpace) ∈
        𝓝[Ico 0 (S + τ) ×ˢ univ] p := by
      filter_upwards [self_mem_nhdsWithin, hnear] with q hq hqS
      exact ⟨⟨hq.1.1, hqS.le⟩, hq.2⟩
    have hreg := (G.contDiffOn_euclideanCoefficients p
      ⟨⟨hp.1.1, ht.le⟩, hp.2⟩).mono_of_mem_nhdsWithin hdom
    apply hreg.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [hnear] with q hq
    exact coefficients_of_lt G H hq q.2
  · have hpos : 0 < p.1 := hS.trans_le (not_lt.mp ht)
    exact (coefficients_smooth_interior G H hS hτ hinit).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hpos, hp.1.2⟩, hp.2⟩)
      |>.contDiffWithinAt



theorem metric_smooth :
    RiemannianMetric.IsSmoothFamilyOn (metric G H) (Ico 0 (S + τ)) := by
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart (fun _ _ => rfl)
    (metric G H) (coefficients G H)
  · have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × StandardCapSpace) ∞
        (fun p : ℝ × StandardCapSpace => (p.1, p.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact (coefficients_smooth G H hS hτ hinit).contMDiffOn.comp hmap.contMDiffOn
      (fun _ hp => hp)
  · intro t _ht x u v
    exact congrArg (fun A => A x u v) (metric_coefficients G H t)

set_option synthInstance.maxHeartbeats 100000 in



theorem metric_equation {t : ℝ} (ht : t ∈ Ico 0 (S + τ))
    (x u v : StandardCapSpace) :
    HasDerivWithinAt (fun s => (metric G H s).inner x u v)
      (-2 * (connection G H t).ricci x u v) (Ico 0 (S + τ)) t := by
  by_cases htS : t < S
  · have hnear : Iio S ∈ 𝓝[Ico 0 (S + τ)] t :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htS)
    have hdom : Icc 0 S ∈ 𝓝[Ico 0 (S + τ)] t := by
      filter_upwards [self_mem_nhdsWithin, hnear] with s hs hsS
      exact ⟨hs.1, hsS.le⟩
    rw [ricci_eq_of_metric_eq (metric_of_lt G H htS) (connection G H t) (G.connection t)]
    have hd := (G.equation t ⟨ht.1, htS.le⟩ x u v).mono_of_mem_nhdsWithin hdom
    apply hd.congr_of_eventuallyEq_of_mem _ ht
    filter_upwards [hnear] with s hs
    rw [metric_of_lt G H hs]
  · have htpos : t ∈ Ioo 0 (S + τ) := ⟨hS.trans_le (not_lt.mp htS), ht.2⟩
    have h := ((hasDerivAt_coefficients G H hS hτ hinit htpos x).clm_apply
      (hasDerivAt_const t u)).clm_apply (hasDerivAt_const t v)
    have hop : jetRicciFlowOperator 3 (spatialJet 2 (coefficients G H) (t, x)) u v =
        -2 * (connection G H t).ricci x u v := by
      rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet,
        ← metric_coefficients G H t]
      exact ricciFlowOperator_metricTwoJet_apply (connection G H t) x u v
    have hfunction : (fun s => (metric G H s).inner x u v) =
        (fun s => coefficients G H (s, x) u v) :=
      funext (fun s => congrArg (fun A => A x u v) (metric_coefficients G H s))
    rw [hfunction]
    simpa only [map_zero, add_zero, zero_add, hop] using h.hasDerivWithinAt



noncomputable def flow : RicciFlow 3 StandardCapSpace (Ico 0 (S + τ)) where
  metric := metric G H
  connection := connection G H
  interval := ordConnected_Ico
  nontrivial := ⟨0, ⟨le_rfl, add_pos hS hτ⟩, S,
    ⟨hS.le, lt_add_of_pos_right S hτ⟩, hS.ne⟩
  smooth := metric_smooth G H hS hτ hinit
  equation t ht x u v := metric_equation G H hS hτ hinit (t := t) ht x u v



theorem flow_complete
    (hG : ∀ t ∈ Icc 0 S, MetricComplete (G.metric t))
    (hH : ∀ t ∈ Ico 0 τ, MetricComplete (H.metric t))
    {t : ℝ} (ht : t ∈ Ico 0 (S + τ)) :
    MetricComplete ((flow G H hS hτ hinit).metric t) := by
  change MetricComplete (metric G H t)
  by_cases htS : t < S
  · rw [metric_of_lt G H htS]
    exact hG t ⟨ht.1, htS.le⟩
  · rw [metric_of_le G H (not_lt.mp htS)]
    exact hH (t - S) ⟨sub_nonneg.mpr (not_lt.mp htS), by linarith [ht.2]⟩



theorem flow_abs_curvature_le {B C : ℝ}
    (hG : ∀ t ∈ Icc 0 S, ∀ x : StandardCapSpace, |(G.connection t).curvatureTensorNorm x| ≤ B)
    (hH : ∀ t ∈ Ico 0 τ, ∀ x : StandardCapSpace, |(H.connection t).curvatureTensorNorm x| ≤ C)
    {t : ℝ} (ht : t ∈ Ico 0 (S + τ)) (x : StandardCapSpace) :
    |((flow G H hS hτ hinit).connection t).curvatureTensorNorm x| ≤ max B C := by
  change |(connection G H t).curvatureTensorNorm x| ≤ max B C
  by_cases htS : t < S
  · rw [curvatureTensorNorm_eq_of_metric_eq
      (metric_of_lt G H htS) (connection G H t) (G.connection t)]
    exact (hG t ⟨ht.1, htS.le⟩ x).trans (le_max_left _ _)
  · rw [curvatureTensorNorm_eq_of_metric_eq
      (metric_of_le G H (not_lt.mp htS)) (connection G H t) (H.connection (t - S))]
    exact (hH (t - S) ⟨sub_nonneg.mpr (not_lt.mp htS), by linarith [ht.2]⟩ x).trans
      (le_max_right _ _)

end PoincareConjecture.M34.FlowJoining
