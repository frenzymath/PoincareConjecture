import PoincareConjecture.Proofs.M47.SeedOldBufferedYoungVolume
import PoincareConjecture.Proofs.M47.SeedOldHistoryVolume
import PoincareConjecture.Proofs.M47.SeedPositiveTestAge
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveCylinderLines

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47 M46

theorem exists_seed_old_buffered_volume_constant
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          SurgeryObservationIsNextEpoch p O →
          SurgeryPrefixControls p F O → SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
          ∀ T : ℝ, T ∈
            Icc (surgeryEpochStart p.i - 1 / 128) (surgeryEpochStart p.i) →
            ∀ x : (F.slice T).carrier, ∀ r : ℝ, 0 < r → r ≤ p.setup.epsilon →
              ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
                ((F.metric T).ball x r),
                (∀ hs y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 hs y) y) →
                (∀ s hs y, y ∈ (F.metric T).ball x r →
                  (F.connection (T + s / 1)).curvatureTensorNorm
                    (test.forward s hs y) ≤ r⁻¹ ^ 2) →
                ENNReal.ofReal (k * r ^ 3) ≤
                  calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  classical
  obtain ⟨A, kYoung, hA, hkYoung, young⟩ := exists_seed_old_buffered_young_physical_volume P S p hp
  let rho := p.r (Fin.last p.i)
  let g := rho ^ 2 / (32 * A)
  have hrho : 0 < rho := p.r_pos _
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hg : 0 < g := by dsimp only [g]; positivity
  obtain ⟨kOld, hkOld, older⟩ := exists_old_history_volume_constant P S p hp hg
  let k := min (p.kappa (Fin.last p.i) / 512) (min kYoung kOld)
  refine ⟨k, lt_min (div_pos (p.kappa_pos _) (by norm_num)) (lt_min hkYoung hkOld), ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hcutoffLast, youngVolume⟩ := young rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hcutoffLast, ?_⟩
  intro F O hEpoch old admissible pinched policy scales overlap T hTend x r hr hrEpsilon
    test hbased hcurv
  have hTH : T < O.H := hTend.2.trans_lt hEpoch.1
  have hT : 0 < T := by
    have hInitial := epochStart_ge_initial p.i
    linarith only [hInitial, hTend.1]
  have hobsT : T ∈ surgeryObservationInterval O := ⟨hT.le, hTH⟩
  have hTF := O.interval_subset hobsT
  have hmono (k' : ℝ) (hle : k ≤ k')
      (hv : ENNReal.ofReal (k' * r ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r)) :
      ENNReal.ofReal (k * r ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (pow_nonneg hr.le 3))).trans hv
  have hxball : x ∈ (F.metric T).ball x r := by
    change (F.metric T).edist x x < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hs0 : -r ^ 2 / 8 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hr)) (by norm_num)
  have hsub : Icc (-r ^ 2 / 8) 0 ⊆ Icc (-r ^ 2) 0 :=
    Icc_subset_Icc (by nlinarith [sq_nonneg r]) le_rfl
  have hwindow : Icc (T + (-r ^ 2 / 8)) T ⊆ surgeryObservationInterval O := by
    intro t ht
    have hparam : t - T ∈ Icc (-r ^ 2 / 8) 0 :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htF : t ∈ F.time_domain := by
      simpa only [div_one, add_sub_cancel] using
        test.time_subset (mem_image_of_mem _ (hsub hparam))
    exact ⟨F.time_domain_nonnegative htF, ht.2.trans_lt hTH⟩
  have hs0mem : -r ^ 2 / 8 ∈ Icc (-r ^ 2) 0 := hsub ⟨le_rfl, hs0.le⟩
  by_cases hpositiveStart : SurgeryPositiveComponentAt F (T + (-r ^ 2 / 8) / 1)
      (test.forward (-r ^ 2 / 8) hs0mem x)
  · have hpositive0 : SurgeryPositiveComponentAt F T x := by
      have hzero : (0 : ℝ) ∈ Icc (-r ^ 2) 0 := ⟨by nlinarith [sq_nonneg r], le_rfl⟩
      have h := positive_component_cylinder_line test hxball hs0mem hzero hs0.le hpositiveStart
      have hpoint : (⟨T + 0 / 1, test.forward 0 hzero x⟩ :
          (t : ℝ) × (F.slice t).carrier) = ⟨T, x⟩ :=
        Sigma.ext (by simp) (hbased hzero x hxball)
      exact (congrArg (fun q : (t : ℝ) × (F.slice t).carrier =>
        SurgeryPositiveComponentAt F q.1 q.2) hpoint).mp h
    obtain ⟨U, _hU, hcompact, hconnected, hxU, b, hb, e, ebased, birth⟩ :=
      exists_seed_component_birth F hTF x
    have hbirthAge := seed_component_birth_le_positive_test P.m04 policy
      hsub hwindow test hbased x hxball hs0.le hpositiveStart U hcompact hconnected hxU
      e hb.2 ebased birth
    obtain ⟨a, ha, G, d, agree, dbased, readout, nonnegative, before, onset⟩ :=
      exists_seed_positive_onset P (hbirthAge.trans_lt hs0) U hcompact hconnected
        ⟨x, hxU⟩ e ebased hpositive0
    have honsetAge := seed_component_onset_le_positive_test hsub test hbased x hxball
      hs0.le hpositiveStart U hxU e ebased hbirthAge before
    have birthAt := seed_onset_birth_alternative U hcompact hconnected e d hb.2
      agree onset birth
    by_cases hyoung : -a ≤ g
    · have hobs : Icc (T + a) T ⊆ surgeryObservationInterval O := by
        intro t ht
        exact ⟨by linarith [hb.1, ha.1, ht.1], ht.2.trans_lt hTH⟩
      have hbound : -a ≤ rho ^ 2 / 32 := hyoung.trans
        (div_le_div_of_nonneg_left (sq_nonneg rho) (by norm_num) (by linarith only [hA]))
      have hrsmall : rho ≤ 1 / 200 :=
        (p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _))
      have hbirthPositive : 0 < T + a / 1 := by
        have hTi := epochStart_ge_initial p.i
        simp only [div_one]
        nlinarith only [hbound, hrsmall, hrho, hTi, hTend.1]
      have hbirth := fun y : U => (birthAt ⟨le_rfl, ha.2.le⟩ y).resolve_left
        (ne_of_gt hbirthPositive)
      exact hmono kYoung ((min_le_right _ _).trans (min_le_left _ _))
        (youngVolume F O hEpoch.1 hEpoch.2 old admissible pinched policy scales overlap
          T a ha.2 hyoung hTend hobs U hcompact hconnected d dbased G
          (fun s hs y => (readout s hs y).1) (fun s hs y => (readout s hs y).2.1)
          (fun s hs y => (readout s hs y).2.2) nonnegative ⟨le_rfl, ha.2.le⟩ hbirth
          ⟨x, hxU⟩ r hr (by linarith only [honsetAge]) test hbased hcurv)
    · have hage : g ≤ -a := (lt_of_not_ge hyoung).le
      have hborn : T + a ≤ surgeryEpochStart p.i - g := by
        linarith only [hage, hTend.2]
      exact hmono kOld ((min_le_right _ _).trans (min_le_right _ _))
        (older F O old pinched policy T a hTH.le (hTH.le.trans hEpoch.2)
          hage hborn U hcompact hconnected d dbased G
          (fun s hs y => (readout s hs y).1) (fun s hs y => (readout s hs y).2.1)
          (fun s hs y => (readout s hs y).2.2) nonnegative birthAt
          ⟨x, hxU⟩ r hr hrEpsilon test hbased hcurv)
  · have hOld : T + (-r ^ 2 / 8) / 1 ∈
        surgeryObservationInterval O ∩ prefixFinalInterval p := by
      have hobs : T + (-r ^ 2 / 8) / 1 ∈ surgeryObservationInterval O := by
        apply hwindow
        simp only [div_one]
        exact ⟨le_rfl, by linarith only [hs0]⟩
      refine ⟨hobs, hobs.1, ?_⟩
      simp only [div_one]
      linarith only [hs0, hTend.2]
    have hre : r ≤ F.parameters.epsilon := by rwa [old.epsilon_eq]
    exact hmono (p.kappa (Fin.last p.i) / 512) (min_le_left _ _)
      (seed_volume_of_near_nonpositive_ancestor P (prefix_noncollapsed old le_rfl)
        x hr hre test hbased hcurv hs0mem le_rfl hOld hpositiveStart)

end PoincareConjecture.Proofs.M47
