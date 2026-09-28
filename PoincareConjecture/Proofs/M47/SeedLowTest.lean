import PoincareConjecture.Proofs.M47.SeedLowScale
import PoincareConjecture.Proofs.M47.SeedLowCylinder
import PoincareConjecture.Proofs.M47.SeedLowComponent
import PoincareConjecture.Proofs.M47.SeedM15CapFloor
import PoincareConjecture.Proofs.M47.SeedVolume
import PoincareConjecture.Proofs.M47.ComponentEstimateProof
import PoincareConjecture.Proofs.M47.BlowupControlsFirstFailure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem exists_seed_low_center_test
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {rNext : ℝ} (hrNext : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i)) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ rNext ∧
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext cutoff F O →
          ∀ T : ℝ, T ∈ surgeryObservationInterval O → surgeryEpochStart p.i ≤ T →
            ∀ x : (F.slice T).carrier,
              (F.connection T).scalarCurvature x ≤ rNext⁻¹ ^ 2 →
              ∃ e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-rho ^ 2) 0)
                ((F.metric T).ball x (2 * rho)),
                (∀ hs y, y ∈ (F.metric T).ball x (2 * rho) → HEq (e.forward 0 hs y) y) ∧
                ∀ s hs y, y ∈ (F.metric T).ball x (2 * rho) →
                  (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤
                    rho⁻¹ ^ 2 := by
  let PA : M47ComponentAnalyticPredecessors.{u} := {
    tensor_calculus := P.m04.tensor_calculus 3
    scalar_regular := P.m04.scalar_regular 3
    scalar_evolution := P.m04.scalar_evolution 3
    local_derivative_estimates := P.m04.local_derivative_estimates 3
    metric_comparison := P.m04.metric_comparison 3
  }
  obtain ⟨B⟩ := componentAnalyticBounds P PA S.setup.C S.setup.C_large
  obtain ⟨Bs, hBs, _hCBs, spatial⟩ := exists_seed_low_center_ball_bound.{u} S.setup.C
  let A := max Bs (max 1 (blowupAnalyticConstant S B))
  have hBsA : Bs ≤ A := le_max_left _ _
  have hA : 1 ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hBA : blowupAnalyticConstant S B ≤ A :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨r0, hr0, hr0Next, h128, hthreshold, hnext, hgap, hr0sq⟩ :=
    exists_seed_low_scalar_scale S.setup.C B.curvature_threshold hrNext
  let d := r0 ^ 2 / (64 * A)
  let rho := smallTestRadius A r0
  have hd : 0 < d := div_pos (sq_pos_of_pos hr0) (by positivity)
  have hdscale : d ≤ r0 ^ 2 := div_le_self (sq_nonneg r0) (by linarith)
  have hrho : 0 < rho := smallTestRadius_pos hA hr0
  have hrhoNext : rho ≤ rNext := (smallTestRadius_le hA hr0).trans hr0Next
  have hbudget : 64 * A * r0⁻¹ ^ 2 * d ≤ 1 := by
    dsimp only [d]
    have heq : 64 * A * r0⁻¹ ^ 2 * (r0 ^ 2 / (64 * A)) = 1 := by
      field_simp [hr0.ne', hApos.ne']
    exact heq.le
  obtain ⟨params⟩ := exists_actionBarrierParameters S p hrho
  obtain ⟨commonCutoff, hcommonPos, hcommonLast, _hcommonScalar, common⟩ :=
    exists_seedM15_commonCutoff P.toM46 S p hp hrNext hrLast hrho params
  let cutoff := min commonCutoff (min (capScalarCutoff p.setup.epsilon params.c r0)
    (B.delta S.setup.standard_initial S.constants))
  have hcutoff : 0 < cutoff := lt_min hcommonPos
    (lt_min (capScalarCutoff_pos p.setup.epsilon_pos params.c_pos hr0) (B.delta_pos _ _))
  have hcommon : cutoff ≤ commonCutoff := min_le_left _ _
  have hscalarCutoff : cutoff ≤ capScalarCutoff p.setup.epsilon params.c r0 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcomponentCutoff : cutoff ≤ B.delta S.setup.standard_initial S.constants :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rho, hrho, hrhoNext, cutoff, hcutoff, hcommon.trans hcommonLast, ?_⟩
  intro F O inputs T hTO hTi x hlow
  have hInitial : F.standard_initial = S.setup.standard_initial := by
    rw [inputs.old.standard_initial_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [inputs.old.C_eq, hp.setup_eq]
  have hPrevious : 1 / 32 ≤ surgeryEpochStart (p.i - 1) := epochStart_ge_initial _
  have hEpoch : surgeryEpochStart p.i = 2 * surgeryEpochStart (p.i - 1) := by
    calc
      surgeryEpochStart p.i = surgeryEpochStart (p.i - 1 + 1) := by
        rw [Nat.sub_add_cancel p.i_pos]
      _ = 2 * surgeryEpochStart (p.i - 1) := by
        unfold surgeryEpochStart
        rw [pow_succ]
        ring
  have hbottom : surgeryEpochStart (p.i - 1) < T - d := by
    rw [hEpoch] at hTi
    linarith only [hTi, hPrevious, hdscale, hr0sq]
  have hwindow : Icc (T - d) T ⊆ surgeryObservationInterval O ∩ overlapInterval p := by
    intro t ht
    have hlo := hbottom.trans_le ht.1
    have hhi := ht.2.trans_lt hTO.2
    exact ⟨⟨by linarith only [hlo, hPrevious], hhi⟩,
      hlo.le, hhi.trans_le inputs.next_epoch.2⟩
  have htime : Icc (T - d) T ⊆ F.time_domain :=
    fun _ ht => O.interval_subset (hwindow ht).1
  have hcanonical : ∀ y ∈ (F.metric T).ball x (r0 / (8 * Bs)),
      r0⁻¹ ^ 2 ≤ (F.connection T).scalarCurvature y →
        SurgeryCanonicalControl F T y F.parameters.epsilon S.setup.C := by
    intro y _hy hhigh
    simpa only [hC] using inputs.canonical T hTO (O.interval_subset hTO) y
      (hnext.trans hhigh)
  have hballScalar := spatial F T x (rNext⁻¹ ^ 2) r0 S.setup.C_pos.le hr0
    hlow hnext hgap hcanonical
  let U := (F.metric T).ball x (r0 / (8 * A))
  have hUopen : IsOpen U := isOpen_Iio.preimage
    ((M36.metric_edist_continuous (F.metric T)).comp
      (continuous_const.prodMk continuous_id))
  have hUcenter : x ∈ U := by
    change (F.metric T).edist x x < ENNReal.ofReal (r0 / (8 * A))
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hr0 (by positivity))
  have hUold : U ⊆ (F.metric T).ball x (r0 / (8 * Bs)) := by
    intro y hy
    apply hy.trans_le (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_left hr0.le (by positivity) (by linarith only [hBsA])
  have hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio T) rNext :=
    fun t ht => inputs.canonical t ht.1
  have hOverlap : ∀ t ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants := by
    intro t ht
    exact (inputs.overlap t ⟨ht.1, ht.2.1, ht.2.2.trans_le inputs.next_epoch.2⟩).trans
      hcomponentCutoff
  have hrate : ∀ t ∈ Ioo (T - d) T, t ∉ F.surgery_times →
      ∀ y : (F.slice t).carrier, r0⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature y →
        |(F.connection t).laplacian (F.connection t).scalarCurvature y +
          2 * (F.connection t).ricciNormSq y| ≤ A * (F.connection t).scalarCurvature y ^ 2 := by
    intro t ht _hnot y hhigh
    have hrecip : 1 / (r0⁻¹ ^ 2) = r0 ^ 2 := by field_simp
    have hs : t ∈ Ico (T - 1 / (r0⁻¹ ^ 2)) T := by
      rw [hrecip]
      exact ⟨by linarith only [ht.1, hdscale], ht.2⟩
    have h := first_failure_physical_analytic_estimate S B p O hInitial
      inputs.old.local_constants_eq hC ⟨hTi, hTO.2⟩ (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num; simpa only [inv_pow] using h128) hthreshold hnext
      inputs.pinched hEarlier hOverlap hs y hhigh
    exact h.2.2.trans (mul_le_mul_of_nonneg_right hBA (sq_nonneg _))
  obtain ⟨_caps, floor, _confine⟩ := common F O (inputs.cutoff_mono hcommon)
  have hcap : ∀ t ∈ Ioc (T - d) T,
      ∀ (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
      ∀ i : Fin (F.event t hT).cap_count,
      ∀ y ∈ ((F.event t hT).caps i).carrier,
        4 * r0⁻¹ ^ 2 < (F.connection t).scalarCurvature y := by
    intro t ht hT _ i y hy
    have hw := hwindow (Ioc_subset_Icc_self ht)
    have hdelta : F.parameters.delta t ≤ capScalarCutoff F.parameters.epsilon params.c r0 := by
      rw [inputs.old.epsilon_eq]
      exact (inputs.overlap t hw).trans hscalarCutoff
    exact (cap_birth_floor_gt_four_inv_sq F hw.1.1 params.c_pos hr0 hdelta).trans_le
      (floor t hT hw.1 hw.2.1 i y hy)
  let P44 : M44CapPersistencePredecessors.{u} :=
    { curvature := P.m04, ordinary_flow := P.m13.ordinary_flow }
  obtain ⟨e, hbased, hscalar⟩ := exists_seed_low_scalar_cylinder P44 inputs.pinched
    hd.le hApos hr0 hbudget htime U hUopen ⟨x, hUcenter⟩
    (fun y hy => hballScalar y (hUold hy)) hrate hcap
  have hr0small : r0 ≤ 1 / 200 := hr0Next.trans (hrLast.trans
    ((p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _))))
  have hcurv := seed_low_cylinder_curvature P.toM46 inputs.pinched hr0 hr0small e hscalar
  have htimeSmall : Icc (-rho ^ 2) 0 ⊆ Icc (-d) 0 := by
    intro s hs
    exact ⟨by linarith only [hs.1, smallTestRadius_sq_le hA hr0], hs.2⟩
  have hspaceSmall : (F.metric T).ball x (2 * rho) ⊆ U := by
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (twice_smallTestRadius_le hA hr0))
  refine ⟨e.restrict htimeSmall ordConnected_Icc hspaceSmall, ?_, ?_⟩
  · exact fun hs y hy => hbased (htimeSmall hs) y (hspaceSmall hy)
  · intro s hs y hy
    exact (hcurv s (htimeSmall hs) y (hspaceSmall hy)).trans
      (fifty_two_inv_sq_le_smallTestRadius_inv_sq hA hr0)

end PoincareConjecture.M47
