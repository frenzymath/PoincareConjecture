import PoincareConjecture.Proofs.M47.OldCapContactVolume
import PoincareConjecture.Proofs.M47.SeedNearbyVolume

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_old_cap_inner_volume (P : M47Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {H r B : ℝ} (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H)
    (hr : 0 < r) (hB : M46.seedAnalyticConstant S ≤ B)
    (htube : 3 * r ≤ (Real.sqrt H)⁻¹ / (8 * B)) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryPrefixControls p F O →
        ∀ T ∈ surgeryObservationInterval O ∩ prefixFinalInterval p,
          ∀ (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier],
            ∀ i : Fin (F.event T hT).cap_count,
              ∀ q z : (F.slice T).carrier, z ∈ ((F.event T hT).caps i).carrier →
                ¬ SurgeryPositiveComponentAt F T q →
                (F.connection T).scalarCurvature q ≤ H →
                (F.connection T).scalarCurvature z ≤ H →
                (F.metric T).edist q z < ENNReal.ofReal (2 * r) →
                ∀ s : ℝ, 0 < s → s ≤ 3 * r →
                  ENNReal.ofReal (k * s ^ 3) ≤ calibratedMetricVolume (F.metric T)
                    ((F.metric T).ball q s) := by
  have hH : 0 < H :=
    (pow_pos (inv_pos.mpr (p.r_pos (Fin.last p.i))) 2).trans_le hlevel
  let Hcap := max H (r⁻¹ ^ 2)
  have hHcap : 0 < Hcap := hH.trans_le (le_max_left _ _)
  obtain ⟨d, k0, hd, hk0, hdcap, hcontact⟩ := exists_old_cap_contact_volume
    P S p compatible Hcap (hlevel.trans (le_max_left _ _))
  have hroot : r⁻¹ ≤ Real.sqrt Hcap := by
    have hsquare : r⁻¹ ^ 2 ≤ Hcap := le_max_right _ _
    have hinverse := inv_pos.mpr hr
    have hsqrt := Real.sqrt_pos.mpr hHcap
    nlinarith [Real.sq_sqrt hHcap.le]
  have hdr : d ≤ r := hdcap.trans (by
    have h := (inv_le_inv₀ (Real.sqrt_pos.mpr hHcap) (inv_pos.mpr hr)).mpr hroot
    simpa only [inv_inv] using h)
  let K := 13 * max (2 * H) (Real.exp 4)
  have hK : 0 < K := mul_pos (by norm_num)
    ((Real.exp_pos 4).trans_le (le_max_right _ _))
  let k := (Real.cosh (3 * r * Real.sqrt K))⁻¹ ^ 2 *
    (k0 * d ^ 3 / (3 * r) ^ 3)
  refine ⟨k, seed_nearby_density_pos hr hd hk0, ?_⟩
  intro F O old T ht hT _ i q z hz hpositive hq hzscalar hclose s hs hsr
  let : CompactSpace (F.slice T).carrier :=
    isCompact_univ_iff.mp (F.slices_compact T (O.interval_subset ht.1))
  have hzpositive : ¬ SurgeryPositiveComponentAt F T z :=
    not_positive_of_mem_component hpositive
      (M46.metric_ball_subset_connectedComponent (F.metric T) q (2 * r) hclose)
  have hvolume := hcontact F O old T ht hT i z hz hzpositive
    (hzscalar.trans (le_max_left _ _))
  have hcurv := seed_ball_curvature_bound P S F T hH hlevel hB
    (old_prefix_seed_canonical S p compatible old ht)
    (old.pinched T ht.1 (O.interval_subset ht.1)) q hpositive hq
  exact seed_nearby_ball_volume (F.metric T) (F.connection T) q z hr hd hdr
    hs hsr hk0 hK hclose (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
    (fun y hy => hcurv y (hy.trans_le (ENNReal.ofReal_le_ofReal htube))) hvolume

end PoincareConjecture.Proofs.M47
