import PoincareConjecture.Proofs.M47.SeedOldRecentCases
import PoincareConjecture.Proofs.M47.SeedM15RecentVolume
import PoincareConjecture.Proofs.M47.SeedRetainedCutoff










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47 M46



theorem exists_positive_retained_volume_constant
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ (rNext rho : ℝ), 0 < rNext →
      rNext ≤ p.r (Fin.last p.i) → 0 < rho →
      ∀ params : ActionBarrierParameters S p rho,
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
            ObservedInputs p rNext cutoff F O →
            ∀ (T : ℝ), 0 < T → T ∈ F.time_domain →
              T ∈ surgeryObservationInterval O → surgeryEpochStart p.i ≤ T →
              ∀ (x : (F.slice T).carrier), SurgeryPositiveComponentAt F T x →
                ∀ (r : ℝ), 0 < r → r ≤ p.setup.epsilon →
                  ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
                    ((F.metric T).ball x r),
                    (∀ hs y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 hs y) y) →
                    (∀ s hs y, y ∈ (F.metric T).ball x r →
                      (F.connection (T + s / 1)).curvatureTensorNorm
                        (test.forward s hs y) ≤ r⁻¹ ^ 2) →
                    ∀ b ∈ Icc (-T) 0,
                    ∀ U : TopologicalSpace.Opens (F.slice T).carrier,
                      IsCompact (U : Set (F.slice T).carrier) → x ∈ U →
                    ∀ e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U,
                      (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) →
                      b < -3 * params.safeTime →
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
    exists_seedRetained_commonCutoff P.toM46 S p hp hrNext hrLast hrho params
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro F O inputs T hT hTF hTO hTi x hpositive r hr hrEps test hbased hcurv
    b hb U hcompact hx e hebased hage
  have hTmax : T ≤ surgeryEpochStart (p.i + 1) := hTO.2.le.trans inputs.next_epoch.2
  rcases oldOrRecent F O inputs.old inputs.pinched inputs.terminal_policy
      T hT hTF hTi hTO.2.le hTmax x hpositive r hr hrEps test hbased hcurv with
    hold | hrecent
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_left kOld (uniform.kappa / 8)) (pow_nonneg hr.le 3))).trans hold
  · obtain ⟨V, hV, hVcompact, hconnected, b', hb', f, fbased, birth, a, ha,
      honsetTime, onset⟩ := hrecent
    obtain ⟨H⟩ := seedM15_testHistory P.toM46 hT hTF x hr test hbased hcurv
    obtain ⟨_caps, birthFloor, confine⟩ := common F O inputs
    obtain ⟨confinement, barrier⟩ := confine T r hT hTF x H hTi hTO.2.le
      b hb U hcompact hx e hebased hage
    let P44 : M44CapPersistencePredecessors.{u} :=
      { curvature := P.m04, ordinary_flow := P.m13.ordinary_flow }
    have hDelta : 2 * g0 ≤ surgeryEpochStart (p.i - 1) / 2 := by
      dsimp only [g0]
      linarith only [hprev]
    have honsetTime' : surgeryEpochStart p.i - (2 * g0) / 2 < T + a / 1 := by
      linarith only [honsetTime]
    have hvolume := seedM15_recent_volume_of_confinement P.toM46 P44 S p hp
      hB hBanalytic params.c_pos hrNext hrLast hscalar hDelta uniform
      inputs H hTO hTi hr hrEps confinement barrier hb' ha V hV hVcompact hconnected
      f fbased birth onset honsetTime' birthFloor
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_right kOld (uniform.kappa / 8)) (pow_nonneg hr.le 3))).trans hvolume

end PoincareConjecture.Proofs.M47
