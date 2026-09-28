import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalPullbackJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalCylinderMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance terminalCylinderJetCoefficientNorm : NormedAddCommGroup
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance terminalCylinderJetCoefficientSpace : NormedSpace ℝ
    (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance terminalCylinderTwoJetNorm : NormedAddCommGroup
    (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance terminalCylinderTwoJetSpace : NormedSpace ℝ
    (MetricTwoJet 3) := Prod.normedSpace

theorem metricTwoJet_const_smul (Q : ℝ) (B : E → MetricCoefficient 3) (x : E) :
    metricTwoJet (Q • B) x = Q • metricTwoJet B x := by
  simp only [metricTwoJet, fderiv_const_smul_field, Pi.smul_apply, Prod.smul_mk]

theorem metricTwoJet_rescaled_pullback
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {Q : ℝ} (hQ : 0 < Q) (f : E → M) (x : E) :
    metricTwoJet ((m01RescaledMetric g Q hQ).pullbackCoefficients f) x =
      Q • metricTwoJet (g.pullbackCoefficients f) x := by
  have heq : (m01RescaledMetric g Q hQ).pullbackCoefficients f =
      Q • g.pullbackCoefficients f := by
    ext y v w
    rfl
  rw [heq, metricTwoJet_const_smul]

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c : ℝ} {U : Set C.carrier}

theorem CylinderRicciFlow.normalized_coefficients_eq
    {e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U}
    {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞}
    (G : CylinderRicciFlow e f) (hmap : f.target ⊆ U)
    (p : (⟨f.target, f.open_target⟩ : Opens C.carrier))
    (s : ℝ) (hs : s ∈ Ico 0 c) {x : E} (hx : x ∈ f.source) :
    (G.flow.metric s).pullbackCoefficients (targetChart f p) x =
      scale • cylinderPhysicalCoefficients e f s hs x := by
  ext v w
  change (G.flow.metric s).pullbackCoefficients (targetChart f p) x v w =
    scale * cylinderPhysicalCoefficients e f s hs x v w
  rw [G.physical_coefficients_eq hmap p s hs hx, ← mul_assoc,
    mul_inv_cancel₀ e.scale_pos.ne', one_mul]

theorem cylinderTerminalChart_twoJet_near_of_tail
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale))
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U)
    (G : CylinderRicciFlow e f)
    (p : (⟨f.target, f.open_target⟩ : Opens C.carrier))
    (hscalar : ∀ x ∈ U, ∃ K : ℝ, ∀ s (hs : s ∈ Ico (0 : ℝ) c),
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K)
    {x : E} (hx : x ∈ f.source) (J : MetricTwoJet 3) {d s0 : ℝ} (hs0 : s0 < c)
    (hbound : ∀ s ∈ Ico (0 : ℝ) c, s0 ≤ s →
      ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x - J‖ ≤ d) :
    ‖metricTwoJet ((m01RescaledMetric (F.event (origin + c / scale) hT).limit_metric
      scale e.scale_pos).pullbackCoefficients
        (cylinderTerminalChart e hU hT r hr hr' ∘ f)) x - J‖ ≤ d := by
  let event := F.event (origin + c / scale) hT
  let A := (event.pre_identify ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ f
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A f.source :=
    (event.pre_identify ⟨origin + r / scale, hr'⟩).symm.contMDiff.comp_contMDiffOn
      ((e.forward_smooth r hr).comp f.contMDiffOn (fun _ hz => hmap (f.map_source hz)))
  have hreg : MapsTo A f.source event.regular_limit := by
    intro y hy
    exact cylinder_preterminal_mem_regular_limit P hpinch e hT r hr hr'
      (hmap (f.map_source hy)) (hscalar _ (hmap (f.map_source hy)))
  change ‖metricTwoJet
    ((m01RescaledMetric event.limit_metric scale e.scale_pos).pullbackCoefficients
      (event.limit_identify.map ∘ A)) x - J‖ ≤ d
  rw [metricTwoJet_rescaled_pullback]
  have hconv := (tendsto_preterminal_pullback_twoJet event f.open_source hA hreg hx).const_smul
    scale
  apply le_of_tendsto (hconv.sub tendsto_const_nhds).norm
  have htail : origin + s0 / scale < origin + c / scale :=
    add_lt_add_right ((div_lt_div_iff_of_pos_right e.scale_pos).mpr hs0) origin
  filter_upwards [Ioo_mem_nhdsLT hr'.2, Ioo_mem_nhdsLT htail] with t ht ht0
  let s := scale * (t - origin)
  have hclock : origin + s / scale = t := by
    dsimp [s]
    field_simp [e.scale_pos.ne']
    ring
  have hrs : r < s := by
    have hrt : r / scale < t - origin := by linarith only [ht.1]
    simpa only [s, mul_comm] using (div_lt_iff₀ e.scale_pos).mp hrt
  have hsc : s < c := by
    have htc : t - origin < c / scale := by linarith only [ht.2]
    simpa only [s, mul_comm] using (lt_div_iff₀ e.scale_pos).mp htc
  have hs : s ∈ Ico (0 : ℝ) c := ⟨hr.1.trans hrs.le, hsc⟩
  have hs0s : s0 ≤ s := by
    have ht0' : s0 / scale < t - origin := by linarith only [ht0.1]
    simpa only [s, mul_comm] using ((div_lt_iff₀ e.scale_pos).mp ht0').le
  have hs' : origin + s / scale ∈ Ico event.tMinus (origin + c / scale) := by
    rw [hclock]
    exact ⟨hr'.1.trans ht.1.le, ht.2⟩
  have heq : (G.flow.metric s).pullbackCoefficients (targetChart f p) =ᶠ[𝓝 x]
      scale • (event.pre_flow.metric t).pullbackCoefficients A := by
    filter_upwards [f.open_source.mem_nhds hx] with y hy
    rw [G.normalized_coefficients_eq hmap p s hs hy,
      cylinderPhysicalCoefficients_eq_preterminal e f.open_source f.contMDiffOn
        (fun _ hz => hmap (f.map_source hz)) hT
        (event_preterminal_surgery_free P F hpinch hT) r hr hr' s hs hs' hy]
    rw [hclock]
    rfl
  have htwo : metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x =
      scale • metricTwoJet ((event.pre_flow.metric t).pullbackCoefficients A) x := by
    rw [← metricTwoJet_const_smul]
    simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
      (heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [← htwo]
  exact hbound s hs hs0s

theorem cylinderTerminalChart_twoJet_near
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale))
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U)
    (G : CylinderRicciFlow e f)
    (p : (⟨f.target, f.open_target⟩ : Opens C.carrier))
    (hscalar : ∀ x ∈ U, ∃ K : ℝ, ∀ s (hs : s ∈ Ico (0 : ℝ) c),
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K)
    {x : E} (hx : x ∈ f.source) (J : MetricTwoJet 3) {d : ℝ}
    (hbound : ∀ s ∈ Ico (0 : ℝ) c,
      ‖metricTwoJet ((G.flow.metric s).pullbackCoefficients (targetChart f p)) x - J‖ ≤ d) :
    ‖metricTwoJet ((m01RescaledMetric (F.event (origin + c / scale) hT).limit_metric
      scale e.scale_pos).pullbackCoefficients
        (cylinderTerminalChart e hU hT r hr hr' ∘ f)) x - J‖ ≤ d :=
  cylinderTerminalChart_twoJet_near_of_tail P hpinch e hU hT r hr hr'
    f hmap G p hscalar hx J (hr.1.trans_lt hr.2) (fun s hs _ => hbound s hs)

end PoincareConjecture.M44
