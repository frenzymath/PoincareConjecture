import PoincareConjecture.Proofs.M47.EventSeedGeometry
import PoincareConjecture.Proofs.M47.SeedTube










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem old_cap_contact_distance_lt
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (i : Fin (F.event T hT).cap_count) {z : (F.slice T).carrier}
    (hz : z ∈ ((F.event T hT).caps i).carrier) :
    (F.metric T).edist z
      ((F.event T hT).local_embed i
        (((F.event T hT).local_result i).collapse ((F.event T hT).necks i).neck.center)) <
      ENNReal.ofReal (2 * p.setup.epsilon *
        (p.setup.standard_initial.cylindrical_end.radius + 5) + 1) := by
  let E := F.event T hT
  have ht0 : 0 ≤ T := F.time_domain_nonnegative (F.surgery_times_subset hT)
  have hd : 0 < F.parameters.delta T := F.parameters.delta_pos T ht0
  have hdhalf : F.parameters.delta T < 1 / 2 := by
    rw [← E.neck_delta i]
    exact (E.necks i).neck.epsilon_lt_half
  have hdsq : F.parameters.delta T ^ 2 ≤ 1 := by nlinarith
  have hheight : (E.necks i).neck.scale ≤ p.setup.epsilon := by
    calc
      _ = F.parameters.h T := E.neck_scale i
      _ ≤ F.parameters.delta T ^ 2 * F.parameters.r T := F.parameters.h_le T ht0
      _ ≤ F.parameters.r T := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hdsq (F.parameters.r_pos T ht0).le
      _ ≤ F.parameters.epsilon := F.parameters.r_le_epsilon T ht0
      _ = p.setup.epsilon := old.epsilon_eq
  have hradius : F.standard_initial.cylindrical_end.radius =
      p.setup.standard_initial.cylindrical_end.radius :=
    congrArg (fun g : StandardInitialMetric => g.cylindrical_end.radius) old.standard_initial_eq
  have hA : 0 < p.setup.standard_initial.cylindrical_end.radius + 5 := by
    linarith [p.setup.standard_initial.cylindrical_end.radius_pos]
  have hL : 0 < 2 * p.setup.epsilon *
      (p.setup.standard_initial.cylindrical_end.radius + 5) + 1 := by
    have he := p.setup.epsilon_pos
    positivity
  have hdistance := event_cap_contact_distance E i hz
  apply hdistance.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hL).mpr
  rw [hradius]
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hheight (by norm_num : (0 : ℝ) ≤ 2)) hA.le
  linarith

end PoincareConjecture.Proofs.M47
