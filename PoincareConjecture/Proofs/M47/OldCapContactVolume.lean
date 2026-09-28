import PoincareConjecture.Proofs.M47.OldCapContactPath
import PoincareConjecture.Proofs.M47.SeedStoppedPath
import PoincareConjecture.Proofs.M47.SeedUniformTransport











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47





theorem exists_old_cap_contact_volume (P : M47Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    (H : ℝ) (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H) :
    ∃ d k : ℝ, 0 < d ∧ 0 < k ∧ d ≤ (Real.sqrt H)⁻¹ ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryPrefixControls p F O →
        ∀ T ∈ surgeryObservationInterval O ∩ prefixFinalInterval p,
          ∀ (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier],
            ∀ i : Fin (F.event T hT).cap_count, ∀ z ∈ ((F.event T hT).caps i).carrier,
              ¬ SurgeryPositiveComponentAt F T z →
              (F.connection T).scalarCurvature z ≤ H →
              ENNReal.ofReal (k * d ^ 3) ≤ calibratedMetricVolume (F.metric T)
                ((F.metric T).ball z d) := by
  let L := 2 * p.setup.epsilon *
    (p.setup.standard_initial.cylindrical_end.radius + 5) + 1
  have hL : 0 < L := by
    have he := p.setup.epsilon_pos
    have hA : 0 < p.setup.standard_initial.cylindrical_end.radius + 5 := by
      linarith [p.setup.standard_initial.cylindrical_end.radius_pos]
    dsimp only [L]
    positivity
  let k0 := min (canonicalSeedDensity S.setup.C) (M46.canonicalSphereVolumeFloor / 512)
  have hk0 : 0 < k0 := lt_min (canonicalSeedDensity_pos _)
    (div_pos M46.canonicalSphereVolumeFloor_pos (by norm_num))
  obtain ⟨d, k, hd, hk, hds, htransport⟩ :=
    exists_old_prefix_uniform_seed_transport P S p compatible H L k0 hlevel hk0
  refine ⟨d, k, hd, hk, hds, ?_⟩
  intro F O old T ht hT _ i z hz hpositive hlow
  let E := F.event T hT
  let c := E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center)
  let : CompactSpace (F.slice T).carrier :=
    isCompact_univ_iff.mp (F.slices_compact T (O.interval_subset ht.1))
  obtain ⟨gamma, hzero, hone, _, hgamma, hspeed⟩ :=
    exists_seed_path_of_distance (F.metric T) z c hL (old_cap_contact_distance_lt old hT i hz)
  obtain ⟨delta, hd1, hcomp, hdelta, hbound, hspeed', hstart⟩ :=
    exists_seed_path_from_crossing_or_end (F.metric T) (F.connection T) gamma hgamma
      (H := H) (L := L) hL.le (by simpa only [hzero] using hlow) hspeed
  have hnotpositive : ¬ SurgeryPositiveComponentAt F T (delta 0) :=
    not_positive_of_mem_component hpositive (by simpa only [hzero] using hcomp)
  have hH : 0 < H :=
    (pow_pos (inv_pos.mpr (p.r_pos (Fin.last p.i))) 2).trans_le hlevel
  have hvolume : ENNReal.ofReal (k0 * d ^ 3) ≤ calibratedMetricVolume (F.metric T)
      ((F.metric T).ball (delta 0) d) := by
    rcases hstart with hcross | hend
    · have hC : F.parameters.C = S.setup.C := by rw [old.C_eq, compatible.setup_eq]
      have hhigh : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤
          (F.connection T).scalarCurvature (delta 0) := by rwa [hcross]
      have hcanon : SurgeryCanonicalControl F T (delta 0)
          F.parameters.epsilon F.parameters.C := by
        rw [hC]
        exact old_prefix_seed_canonical S p compatible old ht (delta 0) hhigh
      have hrhoSmall : p.r (Fin.last p.i) ≤ 1 / 200 :=
        (p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _))
      have hs : 0 < (Real.sqrt H)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hH)
      have hinverse : ((Real.sqrt H)⁻¹)⁻¹ ≤ d⁻¹ := (inv_le_inv₀ hs hd).mpr hds
      have hpower := pow_le_pow_left₀ (inv_nonneg.mpr hs.le) hinverse 2
      rw [inv_inv, Real.sq_sqrt hH.le] at hpower
      have htest : (F.connection T).scalarCurvature (delta 0) ≤ 9 * d⁻¹ ^ 2 := by
        rw [hcross]
        nlinarith [sq_nonneg d⁻¹]
      have hseed := canonical_seed_volume P hcanon hnotpositive (p.r_pos _) hrhoSmall
        hhigh (old.pinched T ht.1 (O.interval_subset ht.1)) hd htest
      rw [hC] at hseed
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hd.le 3))).trans hseed
    · have hcenter : delta 0 = c := hend.trans hone
      have hcenterScalar := event_retained_center_scalar E (F.connection T) i
      have hscalar : (E.necks i).neck.scale⁻¹ ^ 2 ≤ H := by
        have h := hbound 0 ⟨le_rfl, zero_le_one⟩
        rw [hcenter] at h
        change (F.connection T).scalarCurvature
          (E.local_embed i ((E.local_result i).collapse (E.necks i).neck.center)) ≤ H at h
        rwa [hcenterScalar] at h
      have hh := (E.necks i).neck.scale_pos
      have hroot := Real.sqrt_pos.mpr hH
      have hinverse : (E.necks i).neck.scale⁻¹ ≤ Real.sqrt H := by
        have hi := inv_pos.mpr hh
        nlinarith [Real.sq_sqrt hH.le]
      have hscale : (Real.sqrt H)⁻¹ ≤ (E.necks i).neck.scale := by
        have h := (inv_le_inv₀ hroot (inv_pos.mpr hh)).mpr hinverse
        simpa only [inv_inv] using h
      have hseed := event_retained_center_ball_volume E i hd (hds.trans hscale)
      rw [hcenter]
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hd.le 3))).trans hseed
  have h := htransport F O old T ht delta hdelta hnotpositive hbound hspeed' hvolume
  simpa only [hd1, hzero] using h

end PoincareConjecture.Proofs.M47
