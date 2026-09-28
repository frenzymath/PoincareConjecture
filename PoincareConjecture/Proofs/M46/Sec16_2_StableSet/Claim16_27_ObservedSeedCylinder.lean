import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_FullLowBallCylinder
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_ObservedCylinder
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedScales











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46



theorem observed_old_seed_cylinder
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) {B c rNext cutoff : ℝ}
    (hB : 1 ≤ B) (hBanalytic : seedAnalyticConstant S ≤ B) (hc : 0 < c)
    (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {t : ℝ} (ht : t ∈ surgeryObservationInterval O)
    (hmargin : surgeryEpochStart (p.i - 1) + p.setup.epsilon ^ 2 ≤ t)
    (hbefore : t < surgeryEpochStart p.i)
    (x : (F.slice t).carrier) (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hlow : (F.connection t).scalarCurvature x ≤ (p.r (Fin.last p.i))⁻¹ ^ 2)
    (hbirth : ∀ (s : ℝ) (hs : s ∈ F.surgery_times)
      [Nonempty (F.slice s).carrier], s ∈ surgeryObservationInterval O →
      surgeryEpochStart (p.i - 1) ≤ s →
      ∀ i : Fin (F.event s hs).cap_count,
      ∀ y ∈ ((F.event s hs).caps i).carrier,
        c / (2 * (F.parameters.h s) ^ 2) ≤ (F.connection s).scalarCurvature y) :
    ∃ e : SurgeryFlowCylinder F (F.slice t) t 1
      (Icc (-seedCylinderDuration B (p.r (Fin.last p.i))) 0)
      ((F.metric t).ball x (p.r (Fin.last p.i) / (8 * B))),
      (∀ h y, y ∈ (F.metric t).ball x (p.r (Fin.last p.i) / (8 * B)) →
        HEq (e.forward 0 h y) y) ∧
      (∀ s hs y, y ∈ (F.metric t).ball x (p.r (Fin.last p.i) / (8 * B)) →
        (F.connection (t + s / 1)).scalarCurvature (e.forward s hs y) ≤
          4 * (p.r (Fin.last p.i))⁻¹ ^ 2) ∧
      (∀ s hs y, y ∈ (F.metric t).ball x (p.r (Fin.last p.i) / (8 * B)) →
        (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤
          52 * (p.r (Fin.last p.i))⁻¹ ^ 2) := by
  let r := p.r (Fin.last p.i)
  have hrOld : 0 < r := p.r_pos _
  have hrEps : r ≤ p.setup.epsilon := p.r_le_epsilon _
  have hshort : seedCylinderDuration B r ≤ p.setup.epsilon ^ 2 :=
    (seedCylinderDuration_le_radius_sq hB hrOld).trans
      (by nlinarith [p.setup.epsilon_pos])
  have hwindow : Icc (t - seedCylinderDuration B r) t ⊆
      surgeryObservationInterval O ∩ surgeryEpochEntry p.i := by
    intro s hs
    have hlo : surgeryEpochStart (p.i - 1) ≤ s := by linarith [hs.1]
    refine ⟨⟨?_, hs.2.trans_lt ht.2⟩, ?_⟩
    · linarith [epochStart_ge_initial (p.i - 1)]
    · rw [surgeryEpochEntry, if_neg (Nat.ne_of_gt p.i_pos)]
      exact ⟨hlo, hs.2.trans_lt hbefore⟩
  have hfuture : ∃ top : ℝ, t < top ∧ top ∈ F.time_domain := by
    obtain ⟨top, htop, htopH⟩ := exists_between ht.2
    exact ⟨top, htop, O.interval_subset ⟨ht.1.trans htop.le, htopH⟩⟩
  apply exists_full_low_scalar_ball_cylinder P P44 S x inputs.pinched hB hBanalytic
    hrOld (hrEps.trans (p.setup.epsilon_le.trans (min_le_left _ _))) hpositive hlow
    (fun s hs => O.interval_subset (hwindow hs).1) hfuture
  · intro s hs y hy
    have h := inputs.old.canonical (Fin.last p.i) (by simp) s (hwindow hs)
      (O.interval_subset (hwindow hs).1) y hy
    rw [inputs.old.C_eq, hp.setup_eq] at h
    exact h
  · intro s hs hsurgery _ i y hy
    have hw := hwindow (Ioc_subset_Icc_self hs)
    have hepoch := hw.2
    rw [surgeryEpochEntry, if_neg (Nat.ne_of_gt p.i_pos)] at hepoch
    have hoverlap : s ∈ overlapInterval p := by
      refine ⟨hepoch.1, ?_⟩
      rw [epochStart_succ]
      linarith [hepoch.2, epochStart_ge_initial p.i]
    have hdelta : F.parameters.delta s ≤ capScalarCutoff F.parameters.epsilon c rNext := by
      rw [inputs.old.epsilon_eq]
      exact (inputs.overlap s ⟨hw.1, hoverlap⟩).trans hcutoff
    have hfloor := (cap_birth_floor_gt_four_inv_sq F hw.1.1 hc hr hdelta).trans_le
      (hbirth s hsurgery hw.1 hepoch.1 i y hy)
    have hinv : r⁻¹ ≤ rNext⁻¹ := inv_anti₀ hr hrLast
    have hsquare : r⁻¹ ^ 2 ≤ rNext⁻¹ ^ 2 := by
      nlinarith [inv_pos.mpr hrOld, inv_pos.mpr hr]
    exact (mul_le_mul_of_nonneg_left hsquare (by norm_num : (0 : ℝ) ≤ 4)).trans_lt hfloor

end PoincareConjecture.Proofs.M46
