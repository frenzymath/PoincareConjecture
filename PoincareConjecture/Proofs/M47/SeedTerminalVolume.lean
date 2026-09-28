import PoincareConjecture.Proofs.M47.SeedNearAncestorCases
import PoincareConjecture.Proofs.M47.SeedPositiveTestAge
import PoincareConjecture.Proofs.M47.SeedYoungPhysicalVolume
import PoincareConjecture.Proofs.M47.SeedPositiveRetainedVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47 M46

private theorem retained_time_lt_young_age
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    {A rNext : ℝ} (hA : 1 ≤ A) (hrNext : 0 < rNext)
    (params : ActionBarrierParameters S p (rNext / (8 * A))) :
    3 * params.safeTime < rNext ^ 2 / (32 * A) := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hsafe : params.safeTime ≤ rNext ^ 2 / (256 * A ^ 2) := by
    convert params.safeTime_interval using 1
    field_simp
    ring
  have hscaled := (le_div_iff₀ (by positivity : 0 < 256 * A ^ 2)).mp hsafe
  have hAA : A ≤ A ^ 2 := by nlinarith only [hA]
  have hcompare := mul_le_mul_of_nonneg_left hAA params.safeTime_pos.le
  have hprod := mul_pos params.safeTime_pos hApos
  apply (lt_div_iff₀ (by positivity : 0 < 32 * A)).mpr
  nlinarith only [hscaled, hcompare, hprod, sq_pos_of_pos hrNext]

theorem exists_seed_terminal_volume_constant
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        cutoff ≤ (Classical.choice (N.induction p hp)).cutoff rNext ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext cutoff F O →
          ∀ T : ℝ, T ∈ Ico (surgeryEpochStart p.i) O.H →
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
  obtain ⟨k0, hk0, cases0⟩ := exists_volume_or_small_component_positive_ancestry P S N p hp
  obtain ⟨A, kYoung, hA, hkYoung, young⟩ := exists_seed_young_physical_volume P S N p hp
  obtain ⟨kRetained, hkRetained, retained⟩ := exists_positive_retained_volume_constant P S p hp
  let k := min k0 (min kYoung kRetained)
  refine ⟨k, lt_min hk0 (lt_min hkYoung hkRetained), ?_⟩
  intro rNext hrNext hrLast
  let rho := rNext / (8 * A)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hrho : 0 < rho := div_pos hrNext (mul_pos (by norm_num) hApos)
  obtain ⟨params⟩ := exists_actionBarrierParameters S p hrho
  have hretainedTime := retained_time_lt_young_age S p hA hrNext params
  obtain ⟨delta0, hdelta0, hlast0, hcutoff0, generalCases⟩ := cases0 rNext hrNext hrLast
  obtain ⟨deltaYoung, hdeltaYoung, _hlastYoung, youngVolume⟩ := young rNext hrNext hrLast
  obtain ⟨deltaRetained, hdeltaRetained, _hlastRetained, retainedVolume⟩ :=
    retained rNext rho hrNext hrLast hrho params
  let cutoff := min delta0 (min deltaYoung deltaRetained)
  have hsmall0 : cutoff ≤ delta0 := min_le_left _ _
  have hsmallYoung : cutoff ≤ deltaYoung := (min_le_right _ _).trans (min_le_left _ _)
  have hsmallRetained : cutoff ≤ deltaRetained := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cutoff, lt_min hdelta0 (lt_min hdeltaYoung hdeltaRetained),
    hsmall0.trans hlast0, hsmall0.trans hcutoff0, ?_⟩
  intro F O inputs T hTO x r hr hrEpsilon test hbased hcurv
  have hT : 0 < T := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 32)
    (epochStart_ge_initial p.i)).trans_le hTO.1
  have hobsT : T ∈ surgeryObservationInterval O := ⟨hT.le, hTO.2⟩
  have hTF := O.interval_subset hobsT
  have hmono (k' : ℝ) (hle : k ≤ k')
      (hv : ENNReal.ofReal (k' * r ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r)) :
      ENNReal.ofReal (k * r ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (pow_nonneg hr.le 3))).trans hv
  rcases generalCases F O (inputs.cutoff_mono hsmall0) T hobsT hTO.1 x r hr hrEpsilon
      test hbased hcurv with hvolume | ⟨_hrSmall, _hhigh, _hcomponent, hpositive⟩
  · exact hmono k0 (min_le_left _ _) hvolume
  · have hxball : x ∈ (F.metric T).ball x r := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice T).carrier → Type _) :=
        ⟨(F.metric T).toRiemannianMetric⟩
      change Manifold.riemannianEDist (𝓡 3) x x < ENNReal.ofReal r
      simpa only [Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hr
    have hs0 : -r ^ 2 / 8 < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hr))
      (by norm_num)
    have hsub : Icc (-r ^ 2 / 8) 0 ⊆ Icc (-r ^ 2) 0 :=
      Icc_subset_Icc (by nlinarith [sq_nonneg r]) le_rfl
    have hwindow : Icc (T + (-r ^ 2 / 8)) T ⊆ surgeryObservationInterval O := by
      intro t ht
      have hparam : t - T ∈ Icc (-r ^ 2 / 8) 0 :=
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have htF : t ∈ F.time_domain := by
        simpa only [div_one, add_sub_cancel] using
          test.time_subset (mem_image_of_mem _ (hsub hparam))
      exact ⟨F.time_domain_nonnegative htF, ht.2.trans_lt hTO.2⟩
    have hpositive0 : SurgeryPositiveComponentAt F T x := by
      have hs0mem : (0 : ℝ) ∈ Icc (-r ^ 2) 0 := ⟨by nlinarith [sq_nonneg r], le_rfl⟩
      have h := hpositive 0 hs0mem (by linarith only [hs0])
      have hx := hbased hs0mem x hxball
      have hpoint : (⟨T + 0 / 1, test.forward 0 hs0mem x⟩ :
          (t : ℝ) × (F.slice t).carrier) = ⟨T, x⟩ :=
        Sigma.ext (by simp) hx
      exact (congrArg (fun q : (t : ℝ) × (F.slice t).carrier =>
        SurgeryPositiveComponentAt F q.1 q.2) hpoint).mp h
    have hpositiveStart := hpositive (-r ^ 2 / 8) (hsub ⟨le_rfl, hs0.le⟩) le_rfl
    obtain ⟨U, _hU, hcompact, hconnected, hxU, b, hb, e, ebased, birth⟩ :=
      exists_seed_component_birth F hTF x
    have hbirthAge := seed_component_birth_le_positive_test P.m04 inputs.terminal_policy
      hsub hwindow test hbased x hxball hs0.le hpositiveStart U hcompact hconnected hxU
      e hb.2 ebased birth
    obtain ⟨a, ha, G, d, agree, dbased, readout, nonnegative, before, onset⟩ :=
      exists_seed_positive_onset P (hbirthAge.trans_lt hs0) U hcompact hconnected
        ⟨x, hxU⟩ e ebased hpositive0
    have honsetAge := seed_component_onset_le_positive_test hsub test hbased x hxball
      hs0.le hpositiveStart U hxU e ebased hbirthAge before
    by_cases hyoung : -a ≤ rNext ^ 2 / (32 * A)
    · have hobs : Icc (T + a) T ⊆ surgeryObservationInterval O := by
        intro t ht
        exact ⟨by linarith [hb.1, ha.1, ht.1], ht.2.trans_lt hTO.2⟩
      have hbound : -a ≤ rNext ^ 2 / 32 := hyoung.trans
        (div_le_div_of_nonneg_left (sq_nonneg rNext) (by norm_num) (by linarith only [hA]))
      have hrsmall : rNext ≤ 1 / 200 := hrLast.trans
        ((p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _)))
      have hbirthPositive : 0 < T + a / 1 := by
        have hTi := epochStart_ge_initial p.i
        simp only [div_one]
        nlinarith only [hbound, hrsmall, hrNext, hTi, hTO.1]
      have birthAt := seed_onset_birth_alternative U hcompact hconnected e d hb.2
        agree onset birth
      have hbirth := fun y : U => (birthAt ⟨le_rfl, ha.2.le⟩ y).resolve_left
        (ne_of_gt hbirthPositive)
      exact hmono kYoung ((min_le_right _ _).trans (min_le_left _ _))
        (youngVolume F O (inputs.cutoff_mono hsmallYoung) T a ha.2 hyoung hTO hobs U
          hcompact hconnected d dbased G (fun s hs y => (readout s hs y).1)
          (fun s hs y => (readout s hs y).2.1) (fun s hs y => (readout s hs y).2.2)
          nonnegative ⟨le_rfl, ha.2.le⟩ hbirth ⟨x, hxU⟩ r hr
          (by linarith only [honsetAge]) test hbased hcurv)
    · have hage : a < -3 * params.safeTime := by
        linarith only [lt_of_not_ge hyoung, hretainedTime]
      exact hmono kRetained ((min_le_right _ _).trans (min_le_right _ _))
        (retainedVolume F O (inputs.cutoff_mono hsmallRetained) T hT hTF hobsT hTO.1
          x hpositive0 r hr hrEpsilon test hbased hcurv a
          ⟨hb.1.trans ha.1, ha.2.le⟩ U hcompact hxU d dbased hage)

end PoincareConjecture.Proofs.M47
