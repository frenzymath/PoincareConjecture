import PoincareConjecture.Proofs.M47.SeedCapContactDensity
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CapBirth
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_5_OverlapCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open M46

theorem exists_seed_observed_cap_contact_density
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext cutoff F O →
          ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier),
            t ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ t →
            ∀ (i : Fin (F.event t hT).cap_count) (H r : ℝ),
              0 < r → H * r ^ 2 ≤ 1 →
              ∀ z ∈ ((F.event t hT).caps i).carrier,
                (F.connection t).scalarCurvature z ≤ 4 * H →
              ∀ q : (F.slice t).carrier,
                (F.metric t).edist z q ≤ ENNReal.ofReal (2 * r) →
                ∀ s : ℝ, 0 < s → s ≤ r →
                  ENNReal.ofReal (k * s ^ 3) ≤
                    calibratedMetricVolume (F.metric t) ((F.metric t).ball q s) := by
  obtain ⟨capUniqueness⟩ := S.cap_persistence.standard_cap_uniqueness
  obtain ⟨c, hc, hrate⟩ := capUniqueness.scalar_lower_bound
  obtain ⟨A, k, hA, hk, hdensity⟩ :=
    exists_seed_cap_contact_small_density S.standard_initial hc (by norm_num : (0 : ℝ) < 1)
  obtain ⟨eta, heta, hetaHalf, hfloor⟩ := exists_insertedCap_scalarLower_tolerance
    S.cap_persistence hc (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hA hrate
  have hApos : 0 < A := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  refine ⟨k, hk, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hlast, hcaps⟩ :=
    exists_seedCompatibleOverlapCapCutoff S p hp rNext hrNext hrLast A eta (1 / 2)
      hApos heta (by norm_num) (by norm_num)
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro F O inputs t hT hn ht hstart i H r hr hbudget z hz hceiling q hdist s hs hsr
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [inputs.old.standard_initial_eq, hp.setup_eq, S.setup_standard_initial_eq]
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq (O.redecorateTo inputs.old.standard_initial_eq).standard_flow
      S.cap_persistence.standard_cap.flow :=
    (redecorateTo_standard_flow O inputs.old.standard_initial_eq).trans hpflow
  have caps := hcaps F O inputs.next_epoch inputs.old inputs.admissible inputs.pinched
    inputs.scales inputs.canonical inputs.overlap
  have hpersist := caps t hT ht hstart i
  have hscalar := hfloor F hinitial (O.redecorateTo inputs.old.standard_initial_eq)
    hmodel t hT hn i ht.2 hpersist z hz
  exact hdensity F hinitial (O.redecorateTo inputs.old.standard_initial_eq) t hT hn i
    eta (1 / 2) heta hetaHalf (by norm_num) ht.2 hpersist H r hr hbudget z hz hscalar
    hceiling q hdist s hs hsr

end PoincareConjecture.Proofs.M47
