import PoincareConjecture.Proofs.M47.SeedOldRecentCases
import PoincareConjecture.Proofs.M47.SeedM15RecentVolume
import PoincareConjecture.Proofs.M47.SeedM15CapFloor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47 M46

theorem exists_positive_safe_volume_constant
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ (rNext rho : ℝ), 0 < rNext →
      rNext ≤ p.r (Fin.last p.i) → 0 < rho →
      ∀ params : ActionBarrierParameters S p rho,
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
            (_inputs : ObservedInputs p rNext cutoff F O),
            ∀ (T : ℝ) (hT : 0 < T) (hTF : T ∈ F.time_domain),
              T ∈ surgeryObservationInterval O → surgeryEpochStart p.i ≤ T →
              ∀ (x : (F.slice T).carrier), SurgeryPositiveComponentAt F T x →
                ∀ (r : ℝ), 0 < r → r ≤ p.setup.epsilon →
                  ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
                    ((F.metric T).ball x r),
                    (∀ hs y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 hs y) y) →
                    (∀ s hs y, y ∈ (F.metric T).ball x r →
                      (F.connection (T + s / 1)).curvatureTensorNorm
                        (test.forward s hs y) ≤ r⁻¹ ^ 2) →
                    ∀ H : SeedM15TestHistory T hT hTF x r,
                      SeedM15SafeCylinder H rho params.safeTime params.safeTime_pos →
                        ENNReal.ofReal (k * r ^ 3) ≤
                          calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  let g0 := surgeryEpochStart (p.i - 1) / 8
  have hprev : 0 < surgeryEpochStart (p.i - 1) :=
    (by norm_num : (0 : ℝ) < 1 / 32).trans_le (epochStart_ge_initial _)
  have hg0 : 0 < g0 := div_pos hprev (by norm_num)
  obtain ⟨kOld, hkOld, oldOrRecent⟩ := exists_old_volume_or_recent_ancestry P S p hp hg0
  let B := max 1 (seedAnalyticConstant S)
  have hB : 1 ≤ B := le_max_left _ _
  have hBanalytic : seedAnalyticConstant S ≤ B := le_max_right _ _
  obtain ⟨uniform⟩ := exists_seedM15_uniformData P.toM46 p hB
  let k := min kOld (uniform.kappa / 8)
  have hk : 0 < k := lt_min hkOld (div_pos uniform.kappa_pos (by norm_num))
  refine ⟨k, hk, ?_⟩
  intro rNext rho hrNext hrLast hrho params
  obtain ⟨cutoff, hcutoff, hlast, hscalar, common⟩ :=
    exists_seedM15_commonCutoff P.toM46 S p hp hrNext hrLast hrho params
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro F O inputs T hT hTF hTO hTi x hpositive r hr hrEps test hbased hcurv H safe
  have hTmax : T ≤ surgeryEpochStart (p.i + 1) := hTO.2.le.trans inputs.next_epoch.2
  rcases oldOrRecent F O inputs.old inputs.pinched inputs.terminal_policy
      T hT hTF hTi hTO.2.le hTmax x hpositive r hr hrEps test hbased hcurv with
    hold | hrecent
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_left kOld (uniform.kappa / 8)) (pow_nonneg hr.le 3))).trans hold
  · obtain ⟨U, hU, hcompact, hconnected, b, hb, e, ebased, birth, a, ha,
      hage, onset⟩ := hrecent
    obtain ⟨_caps, birthFloor, confine⟩ := common F O inputs
    obtain ⟨confinement, barrier⟩ := confine T r hT hTF x H hTi hTO.2.le safe
    let P44 : M44CapPersistencePredecessors.{u} :=
      { curvature := P.m04, ordinary_flow := P.m13.ordinary_flow }
    have hDelta : 2 * g0 ≤ surgeryEpochStart (p.i - 1) / 2 := by
      dsimp only [g0]
      linarith only [hprev]
    have hage' : surgeryEpochStart p.i - (2 * g0) / 2 < T + a / 1 := by
      linarith only [hage]
    have hvolume := seedM15_recent_volume_of_confinement P.toM46 P44 S p hp
      hB hBanalytic params.c_pos hrNext hrLast hscalar hDelta uniform
      inputs H hTO hTi hr hrEps confinement barrier hb ha U hU hcompact hconnected
      e ebased birth onset hage' birthFloor
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_right kOld (uniform.kappa / 8)) (pow_nonneg hr.le 3))).trans hvolume

theorem exists_positive_large_test_volume_constant
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ (rNext rho : ℝ), 0 < rNext →
      rNext ≤ p.r (Fin.last p.i) → 0 < rho →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext cutoff F O →
          ∀ (T : ℝ), 0 < T → T ∈ F.time_domain →
            T ∈ surgeryObservationInterval O → surgeryEpochStart p.i ≤ T →
            ∀ (x : (F.slice T).carrier), SurgeryPositiveComponentAt F T x →
              ∀ (r : ℝ), 0 < r → r ≤ p.setup.epsilon → rho ≤ r →
                ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
                  ((F.metric T).ball x r),
                  (∀ hs y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 hs y) y) →
                  (∀ s hs y, y ∈ (F.metric T).ball x r →
                    (F.connection (T + s / 1)).curvatureTensorNorm
                      (test.forward s hs y) ≤ r⁻¹ ^ 2) →
                  ENNReal.ofReal (k * r ^ 3) ≤
                    calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  obtain ⟨k, hk, volume⟩ := exists_positive_safe_volume_constant P S p hp
  refine ⟨k, hk, ?_⟩
  intro rNext rho hrNext hrLast hrho
  obtain ⟨params⟩ := exists_actionBarrierParameters S p hrho
  obtain ⟨cutoff, hcutoff, hlast, hvolume⟩ := volume rNext rho hrNext hrLast hrho params
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro F O inputs T hT hTF hTO hTi x hpositive r hr hrEps hlarge test hbased hcurv
  obtain ⟨H⟩ := seedM15_testHistory P.toM46 hT hTF x hr test hbased hcurv
  obtain ⟨safe⟩ := seedM15_safeCylinder P.toM46 H inputs.pinched hr test hbased hcurv
    hrho hlarge params.safeTime_pos params.safeTime_interval params.safeTime_metric
  exact hvolume F O inputs T hT hTF hTO hTi x hpositive r hr hrEps test hbased hcurv H safe

end PoincareConjecture.Proofs.M47
