import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalMetric
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderRicciFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderPreterminalCoefficients










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}




theorem CylinderRicciFlow.physical_coefficients_eq
    {e : SurgeryFlowCylinder F C origin scale I U}
    {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞}
    (G : CylinderRicciFlow e f) (hmap : f.target ⊆ U)
    (p : (⟨f.target, f.open_target⟩ : Opens C.carrier))
    (s : ℝ) (hs : s ∈ I) {x : E} (hx : x ∈ f.source) (v w : E) :
    cylinderPhysicalCoefficients e f s hs x v w = scale⁻¹ *
      (G.flow.metric s).pullbackCoefficients (targetChart f p) x v w := by
  have heq : e.forward s hs ∘ f =ᶠ[𝓝 x]
      cylinderTargetTransport e f s hs ∘ targetChart f p := by
    filter_upwards [f.open_source.mem_nhds hx] with y hy
    change e.forward s hs (f y) = e.forward s hs (targetChart f p y).1
    rw [targetChart_val f p hy]
  have hdf := ((contMDiffOn_targetChart f p).contMDiffAt
    (f.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdt := (cylinderTargetTransport_smooth e f hmap s hs).mdifferentiable (by simp)
    (targetChart f p x)
  change (F.metric (origin + s / scale)).pullbackCoefficients (e.forward s hs ∘ f)
    x v w = _
  rw [pullbackCoefficients_congr_of_eventuallyEq _ heq]
  change (F.metric (origin + s / scale)).inner
    (cylinderTargetTransport e f s hs (targetChart f p x))
    (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs ∘ targetChart f p) x v)
    (mfderiv (𝓡 3) (𝓡 3) (cylinderTargetTransport e f s hs ∘ targetChart f p) x w) = _
  rw [mfderiv_comp x hdt hdf]
  exact G.physical_metric_link s hs _ _ _




theorem cylinderTerminalChart_quadratic_le
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    {c : ℝ} (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
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
    {x : E} (hx : x ∈ f.source) (v : E) {L : ℝ}
    (hbound : ∀ s (_hs : s ∈ Ico (0 : ℝ) c),
      (G.flow.metric s).pullbackCoefficients (targetChart f p) x v v ≤ L) :
    (F.event (origin + c / scale) hT).limit_metric.pullbackCoefficients
      (cylinderTerminalChart e hU hT r hr hr' ∘ f) x v v ≤ scale⁻¹ * L := by
  let event := F.event (origin + c / scale) hT
  let A := (event.pre_identify ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ f
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A f.source :=
    (event.pre_identify ⟨origin + r / scale, hr'⟩).symm.contMDiff.comp_contMDiffOn
      ((e.forward_smooth r hr).comp f.contMDiffOn (fun _ hz => hmap (f.map_source hz)))
  have hreg : A x ∈ event.regular_limit :=
    cylinder_preterminal_mem_regular_limit P hpinch e hT r hr hr'
      (hmap (f.map_source hx)) (hscalar _ (hmap (f.map_source hx)))
  change event.limit_metric.pullbackCoefficients (event.limit_identify.map ∘ A)
    x v v ≤ scale⁻¹ * L
  apply terminal_pullback_quadratic_le event (hA.contMDiffAt (f.open_source.mem_nhds hx))
    hreg v
  filter_upwards [Ioo_mem_nhdsLT hr'.2] with t ht
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
  have hs' : origin + s / scale ∈ Ico event.tMinus (origin + c / scale) := by
    rw [hclock]
    exact ⟨hr'.1.trans ht.1.le, ht.2⟩
  have heq := cylinderPhysicalCoefficients_eq_preterminal e f.open_source f.contMDiffOn
    (fun _ hz => hmap (f.map_source hz)) hT (event_preterminal_surgery_free P F hpinch hT)
    r hr hr' s hs hs' hx
  have hread : (event.pre_flow.metric t).pullbackCoefficients A x v v =
      scale⁻¹ * (G.flow.metric s).pullbackCoefficients (targetChart f p) x v v := by
    rw [← hclock, ← heq]
    exact G.physical_coefficients_eq hmap p s hs hx v v
  rw [hread]
  exact mul_le_mul_of_nonneg_left (hbound s hs) (inv_pos.mpr e.scale_pos).le




theorem CylinderRicciFlow.pullback_quadratic_le_initial
    (P : M44CapPersistencePredecessors.{u}) {c K : ℝ} (hK : 0 ≤ K)
    {e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U}
    {f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞}
    (G : CylinderRicciFlow e f)
    (hcurv : ∀ s ∈ Ico (0 : ℝ) c, ∀ y, (G.flow.connection s).curvatureTensorNorm y ≤ K)
    (p : (⟨f.target, f.open_target⟩ : Opens C.carrier))
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) c) (x v : E) :
    (G.flow.metric s).pullbackCoefficients (targetChart f p) x v v ≤
      Real.exp (6 * K * c) * (G.flow.metric 0).pullbackCoefficients
        (targetChart f p) x v v := by
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) c := ⟨le_rfl, hs.1.trans_lt hs.2⟩
  have h := (P.curvature.metric_comparison 3 _ (Ico 0 c) G.flow 0 s K h0 hs hs.1 hK
    (fun t ht => hcurv t ⟨ht.1, ht.2.trans_lt hs.2⟩)
    (targetChart f p x) (mfderiv (𝓡 3) (𝓡 3) (targetChart f p) x v)).2
  change (G.flow.metric s).pullbackCoefficients (targetChart f p) x v v ≤
    Real.exp (2 * (3 : ℝ) * K * (s - 0)) *
      (G.flow.metric 0).pullbackCoefficients (targetChart f p) x v v at h
  have hnonneg : 0 ≤ (G.flow.metric 0).pullbackCoefficients (targetChart f p) x v v := by
    change 0 ≤ (G.flow.metric 0).inner (targetChart f p x)
      (mfderiv (𝓡 3) (𝓡 3) (targetChart f p) x v)
      (mfderiv (𝓡 3) (𝓡 3) (targetChart f p) x v)
    by_cases hv : mfderiv (𝓡 3) (𝓡 3) (targetChart f p) x v = 0
    · rw [hv, map_zero]
    · exact ((G.flow.metric 0).pos _ _ hv).le
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hnonneg
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hs.2.le (by positivity : 0 ≤ 6 * K)]

end PoincareConjecture.M44
