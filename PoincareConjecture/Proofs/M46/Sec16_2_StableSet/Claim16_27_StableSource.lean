import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedPaths
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_ObservedSeedCylinder
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_ReducedVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

theorem stableSource_of_observed_cap_birth
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) {B c rNext cutoff : ℝ}
    (hB : 1 ≤ B) (hBanalytic : seedAnalyticConstant S ≤ B) (hc : 0 < c)
    (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D)
    (hTlo : surgeryEpochStart p.i ≤ D.time)
    (C : ActionConfinement H.spacetime.geometry.toLGeometry
      D.time (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val)
    (hbarrier : C.barrier = actionBudget p)
    (M : MinimizingRegion H.spacetime.geometry.toLGeometry
      D.time (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val C)
    (positive : PositiveAncestorExclusion H)
    (hbirth : ∀ (s : ℝ) (hs : s ∈ F.surgery_times)
      [Nonempty (F.slice s).carrier], s ∈ surgeryObservationInterval O →
      surgeryEpochStart (p.i - 1) ≤ s →
      ∀ i : Fin (F.event s hs).cap_count,
      ∀ y ∈ ((F.event s hs).caps i).carrier,
        c / (2 * (F.parameters.h s) ^ 2) ≤ (F.connection s).scalarCurvature y) :
    Nonempty (StableSource H (surgeryEpochStart (p.i + 1))
      (actionBudget p / (4 * p.setup.epsilon))
      (p.kappa (Fin.last p.i) * seedImageRadius B (p.r (Fin.last p.i)) ^ 3 / 8)) := by
  let G := H.spacetime.geometry.toLGeometry
  let r := p.r (Fin.last p.i)
  let d := seedImageDelay B r
  have hrOld : 0 < r := p.r_pos _
  have hd : 0 < d := seedImageDelay_pos hB hrOld
  have hdEps : d ≤ p.setup.epsilon ^ 2 := by
    apply (seedImageDelay_lt_duration hB hrOld).le.trans
    apply (seedCylinderDuration_le_radius_sq hB hrOld).trans
    exact (sq_le_sq₀ hrOld.le p.setup.epsilon_pos.le).mpr (p.r_le_epsilon _)
  have hThi : D.time ≤ surgeryEpochStart (p.i + 1) :=
    D.time_mem.2.le.trans inputs.next_epoch.2
  obtain ⟨endpoint, path, hmin, hshort, tau, htauWindow, hbefore, hlow⟩ :=
    H.low_scalar_minimizer P p inputs.old hTlo hThi C M
  have htauEps : p.setup.epsilon ^ 2 ≤ tau :=
    (le_max_left _ _).trans htauWindow.1
  have htau : 0 < tau := (sq_pos_of_pos p.setup.epsilon_pos).trans_le htauEps
  have htauS : tau ≤ D.time - surgeryEpochStart (p.i - 1) := by
    linarith [htauWindow.2, sq_nonneg p.setup.epsilon]
  have hmargin : surgeryEpochStart (p.i - 1) + p.setup.epsilon ^ 2 ≤ D.time - tau := by
    linarith [htauWindow.2]
  have htobs : D.time - tau ∈ surgeryObservationInterval O := by
    refine ⟨?_, ?_⟩
    · linarith [epochStart_ge_initial (p.i - 1), sq_nonneg p.setup.epsilon]
    · exact (sub_lt_self _ htau).trans D.time_mem.2
  have htold : D.time - tau ∈ surgeryObservationInterval O ∩ surgeryEpochEntry p.i :=
    ⟨htobs, prefix_seed_time_slab p htauWindow.2 hbefore
      ⟨by linarith [sq_nonneg p.setup.epsilon], le_rfl⟩⟩
  have htime0 : D.time - tau ∈ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    exact ⟨htobs.1, sub_le_self _ htau.le⟩
  let q0 : (G.slices (D.time - tau)).Point :=
    ⟨path.curve tau, path.curve_time tau ⟨htau.le, htauS⟩⟩
  let y0 := (H.spacetime.geometry.sliceIdentification (D.time - tau)).identification.symm q0
  let x0 := H.spacetime.history.history.forward (D.time - tau) htime0 y0
  have hlabel :
      ((H.spacetime.geometry.sliceIdentification (D.time - tau)).identification y0).val =
        path.curve tau := by
    exact congrArg Subtype.val
      ((H.spacetime.geometry.sliceIdentification (D.time - tau)).identification.apply_symm_apply q0)
  have hpoint : path.curve tau =
      (⟨D.time - tau, y0⟩ : H.spacetime.geometry.toLGeometry.Point) :=
    hlabel.symm.trans
      ((H.spacetime.geometry.sliceIdentification (D.time - tau)).identification_eq y0)
  have hpositive : ¬ SurgeryPositiveComponentAt F (D.time - tau) x0 := by
    apply positive tau htau htime0 y0
    rw [hlabel]
    exact ⟨M14.prefixPath path tau htau htauS⟩
  have hlowPhysical : (F.connection (D.time - tau)).scalarCurvature x0 ≤ r⁻¹ ^ 2 := by
    rw [hpoint] at hlow
    change horizontalScalarCurvature H.spacetime.geometry.leafwise
      (⟨D.time - tau, y0⟩ : H.spacetime.history.generalized.point) < r⁻¹ ^ 2 at hlow
    rw [M13.originalSlice_scalar H.spacetime.geometry P.m13,
      ← H.spacetime.history.scalar_pullback (D.time - tau) htime0] at hlow
    exact hlow.le
  obtain ⟨e, hbase, hscalar, hRm⟩ := observed_old_seed_cylinder P P44 S p hp
    hB hBanalytic hc hr hrLast hcutoff inputs htobs hmargin hbefore x0 hpositive hlowPhysical
    hbirth
  have htime : ∀ s ∈ Icc (-d) 0,
      (D.time - tau) + s / 1 ∈ H.spacetime.history.generalized.interval := by
    intro s hs
    rw [H.spacetime.history.interval_eq]
    simp only [div_one]
    constructor <;> linarith [hs.1, hs.2, epochStart_ge_initial (p.i - 1)]
  have hStime : D.time - surgeryEpochStart (p.i - 1) ≤ D.time := by
    linarith [epochStart_ge_initial (p.i - 1)]
  have hwindow :
      Icc (D.time - (D.time - surgeryEpochStart (p.i - 1))) D.time ⊆
        H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro t ht
    refine ⟨?_, ht.2⟩
    linarith [ht.1, epochStart_ge_initial (p.i - 1)]
  have hfloor := regular_history_path_scalar_lower P inputs.old H.spacetime path
    D.time_mem hStime hwindow
  have htotalStart : tau + d ≤ D.time - surgeryEpochStart (p.i - 1) := by
    linarith [htauWindow.2]
  have htotalTop : tau + d ≤ surgeryEpochStart (p.i + 1) :=
    htotalStart.trans (hStime.trans hThi)
  obtain ⟨A, hA, hne, hvolume, hpaths⟩ := seed_image_comparisons P P44 p inputs.old
    inputs.pinched H.spacetime hB path hmin htau htauS (hStime.trans hThi) htotalTop
    hfloor hshort htold htime htime0 y0 x0 rfl hpoint hpositive e hbase hscalar hRm
  have hinterior : D.time - (tau + d) ∈ interior H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    change D.time - (tau + d) ∈ interior (Icc (0 : ℝ) D.time)
    rw [interior_Icc]
    constructor
    · linarith [epochStart_ge_initial (p.i - 1)]
    · linarith
  exact stableSource_of_actual_seed_comparisons P p inputs.old H C hbarrier M
    (by linarith : p.setup.epsilon ^ 2 ≤ tau + d) htotalStart htotalTop hinterior A hA hne
    hvolume (fun q hq => by
      obtain ⟨comparison, hcomparison⟩ := hpaths q hq
      exact ⟨comparison, hcomparison.le⟩)

end PoincareConjecture.Proofs.M46
