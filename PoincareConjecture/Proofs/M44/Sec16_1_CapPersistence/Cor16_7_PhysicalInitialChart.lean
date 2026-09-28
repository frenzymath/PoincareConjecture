import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_AmbientBalls
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_InitialChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_AdjustedComparison











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture



theorem SurgeryCapClose.isCompact_closure_image_ball
    {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}
    (Q : SurgeryCapClose g₀ S g tip scale eta)
    {r : ℝ} (hr : 0 < r) (hrEta : r < eta⁻¹) :
    IsCompact (closure (Q.map '' g₀.metric.ball 0 r)) := by
  rw [Q.closure_image_ball hr hrEta]
  apply (M36.standard_closed_ball_compact g₀ hr.le).image_of_continuousOn
  apply Q.map_smooth.continuousOn.mono
  intro x hx
  exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr Q.eta_pos)).mpr hrEta)




theorem local_result_ball_image
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure (((F.event t hT).local_result i).metric.ball
      ((F.event t hT).local_result i).tip r))) :
    (F.event t hT).local_embed i '' ((F.event t hT).local_result i).metric.ball
      ((F.event t hT).local_result i).tip r =
        (F.metric t).ball ((F.event t hT).caps i).tip r := by
  let E := F.event t hT
  let : Nonempty (E.local_result i).output.carrier := ⟨(E.local_result i).tip⟩
  have h := (E.local_result i).metric.image_ball_of_precompact_pullback (F.metric t)
    (E.local_embed_smooth i) (E.local_embed_injective i) (E.local_metric i)
    (E.local_result i).tip hr hcompact
  simpa only [E.local_tip i] using h





theorem initial_cap_chart_of_exact_comparison
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {A eta : ℝ} (hA : 0 < A) (hAeta : A < eta⁻¹)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output
      ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip
      (((F.event t hT).necks i).neck.scale) eta)
    (hdelta : ((F.event t hT).necks i).neck.epsilon ≤
      F.local_constants.comparison_delta eta)
    (hball : Q.map '' F.standard_initial.metric.ball 0 A =
      ((F.event t hT).local_result i).metric.ball ((F.event t hT).local_result i).tip
        (((F.event t hT).necks i).neck.scale * A)) :
    ∃ initial : SurgeryCapInitialComparison F t hT i A,
      initial.chart '' F.standard_initial.metric.ball 0 A =
        (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) := by
  have hcompact := Q.isCompact_closure_image_ball hA hAeta
  rw [hball] at hcompact
  obtain ⟨initial, himage⟩ := initial_cap_chart_of_comparison F t hT i hA hAeta.le Q hdelta
  refine ⟨initial, ?_⟩
  rw [himage, ← image_image, hball,
    local_result_ball_image F t hT i (mul_pos Q.scale_pos hA) hcompact,
    (F.event t hT).neck_scale i, mul_comm]

end PoincareConjecture
