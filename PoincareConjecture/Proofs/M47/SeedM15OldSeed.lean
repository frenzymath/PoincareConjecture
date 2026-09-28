import PoincareConjecture.Proofs.M47.SeedM15LowPoint
import PoincareConjecture.Proofs.M47.SeedM15PathPositivity
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_ObservedSeedCylinder
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SeedPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem seedM15_oldSeed
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) {B c rNext cutoff : ℝ}
    (hB : 1 ≤ B) (hBanalytic : seedAnalyticConstant S ≤ B) (hc : 0 < c)
    (hrNext : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain} {x : (F.slice T).carrier}
    (H : SeedM15TestHistory T hT hTF x r) (hTH : T ≤ O.H)
    {endpoint : H.spacetime.geometry.toLGeometry.Point}
    (path : M14BackwardPath H.spacetime.geometry.toLGeometry T 0
      (T - surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val endpoint)
    (hmin : M14IsMinimizing path)
    (hshort : M14BackwardLAction H.spacetime.geometry.toLGeometry path ≤
      3 * Real.sqrt (T - surgeryEpochStart (p.i - 1)))
    {tau : ℝ}
    (htauWindow : tau ∈ Icc (max (p.setup.epsilon ^ 2) (T - surgeryEpochStart p.i))
      (T - surgeryEpochStart (p.i - 1) - p.setup.epsilon ^ 2))
    (hbefore : T - tau < surgeryEpochStart p.i)
    (hlow : horizontalScalarCurvature H.spacetime.geometry.toLGeometry.leafwise
      (path.curve tau) < (p.r (Fin.last p.i))⁻¹ ^ 2)
    (hnonpositive : ¬ HistoryPositive H.spacetime.history.history (path.curve tau))
    (hbirth : ∀ (s : ℝ) (hs : s ∈ F.surgery_times) [Nonempty (F.slice s).carrier],
      s ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ s →
      ∀ i : Fin (F.event s hs).cap_count, ∀ y ∈ ((F.event s hs).caps i).carrier,
        c / (2 * (F.parameters.h s) ^ 2) ≤ (F.connection s).scalarCurvature y) :
    p.setup.epsilon ^ 2 ≤ tau + seedImageDelay B (p.r (Fin.last p.i)) ∧
    tau + seedImageDelay B (p.r (Fin.last p.i)) ≤ T - surgeryEpochStart (p.i - 1) ∧
    tau + seedImageDelay B (p.r (Fin.last p.i)) ≤ surgeryEpochStart (p.i + 1) ∧
    T - (tau + seedImageDelay B (p.r (Fin.last p.i))) ∈
      interior H.spacetime.history.generalized.interval ∧
    ∃ A : Set (H.spacetime.geometry.toLGeometry.slices
        (T - (tau + seedImageDelay B (p.r (Fin.last p.i))))).Point,
      IsOpen A ∧ A.Nonempty ∧
      ENNReal.ofReal (p.kappa (Fin.last p.i) *
        seedImageRadius B (p.r (Fin.last p.i)) ^ 3 / 8) ≤
        calibratedMetricVolume (H.spacetime.geometry.toLGeometry.slices
          (T - (tau + seedImageDelay B (p.r (Fin.last p.i))))).metricOnPoints A ∧
      ∀ q ∈ closure A, ∃ comparison : M14BackwardPath H.spacetime.geometry.toLGeometry T 0
          (tau + seedImageDelay B (p.r (Fin.last p.i)))
          ((H.spacetime.geometry.sliceIdentification T).identification H.center).val q.val,
        M14BackwardLAction H.spacetime.geometry.toLGeometry comparison < actionBudget p / 2 := by
  let G := H.spacetime.geometry.toLGeometry
  let rOld := p.r (Fin.last p.i)
  let d := seedImageDelay B rOld
  have hrOld : 0 < rOld := p.r_pos _
  have hd : 0 < d := seedImageDelay_pos hB hrOld
  have hdEps : d ≤ p.setup.epsilon ^ 2 := by
    apply (seedImageDelay_lt_duration hB hrOld).le.trans
    apply (seedCylinderDuration_le_radius_sq hB hrOld).trans
    exact (sq_le_sq₀ hrOld.le p.setup.epsilon_pos.le).mpr (p.r_le_epsilon _)
  have hThi : T ≤ surgeryEpochStart (p.i + 1) := hTH.trans inputs.next_epoch.2
  have htauEps : p.setup.epsilon ^ 2 ≤ tau :=
    (le_max_left _ _).trans htauWindow.1
  have htau : 0 < tau := (sq_pos_of_pos p.setup.epsilon_pos).trans_le htauEps
  have htauS : tau ≤ T - surgeryEpochStart (p.i - 1) := by
    linarith [htauWindow.2, sq_nonneg p.setup.epsilon]
  have hmargin : surgeryEpochStart (p.i - 1) + p.setup.epsilon ^ 2 ≤ T - tau := by
    linarith [htauWindow.2]
  have htobs : T - tau ∈ surgeryObservationInterval O := by
    refine ⟨?_, (sub_lt_self _ htau).trans_le hTH⟩
    linarith [epochStart_ge_initial (p.i - 1), sq_nonneg p.setup.epsilon]
  have htold : T - tau ∈ surgeryObservationInterval O ∩ surgeryEpochEntry p.i :=
    ⟨htobs, prefix_seed_time_slab p htauWindow.2 hbefore
      ⟨by linarith [sq_nonneg p.setup.epsilon], le_rfl⟩⟩
  have htime0 : T - tau ∈ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    exact ⟨htobs.1, sub_le_self _ htau.le⟩
  let q0 : (G.slices (T - tau)).Point :=
    ⟨path.curve tau, path.curve_time tau ⟨htau.le, htauS⟩⟩
  let y0 := (H.spacetime.geometry.sliceIdentification (T - tau)).identification.symm q0
  let x0 := H.spacetime.history.history.forward (T - tau) htime0 y0
  have hlabel :
      ((H.spacetime.geometry.sliceIdentification (T - tau)).identification y0).val =
        path.curve tau := congrArg Subtype.val
      ((H.spacetime.geometry.sliceIdentification (T - tau)).identification.apply_symm_apply q0)
  have hpoint : path.curve tau =
      (⟨T - tau, y0⟩ : H.spacetime.geometry.toLGeometry.Point) :=
    hlabel.symm.trans
      ((H.spacetime.geometry.sliceIdentification (T - tau)).identification_eq y0)
  have hpositive : ¬ SurgeryPositiveComponentAt F (T - tau) x0 := by
    intro hpos
    apply hnonpositive
    rw [hpoint]
    exact fun _ => hpos
  have hlowPhysical : (F.connection (T - tau)).scalarCurvature x0 ≤ rOld⁻¹ ^ 2 := by
    rw [hpoint] at hlow
    change horizontalScalarCurvature H.spacetime.geometry.leafwise
      (⟨T - tau, y0⟩ : H.spacetime.history.generalized.point) < rOld⁻¹ ^ 2 at hlow
    rw [Proofs.M13.originalSlice_scalar H.spacetime.geometry P.m13,
      ← H.spacetime.history.scalar_pullback (T - tau) htime0] at hlow
    exact hlow.le
  obtain ⟨e, hbase, hscalar, hRm⟩ := observed_old_seed_cylinder P P44 S p hp
    hB hBanalytic hc hrNext hrLast hcutoff inputs htobs hmargin hbefore x0 hpositive
    hlowPhysical hbirth
  have htime : ∀ s ∈ Icc (-d) 0,
      (T - tau) + s / 1 ∈ H.spacetime.history.generalized.interval := by
    intro s hs
    rw [H.spacetime.history.interval_eq]
    simp only [div_one]
    constructor <;> linarith [hs.1, hs.2, epochStart_ge_initial (p.i - 1)]
  have hStime : T - surgeryEpochStart (p.i - 1) ≤ T := by
    linarith [epochStart_ge_initial (p.i - 1)]
  have hwindow : Icc (T - (T - surgeryEpochStart (p.i - 1))) T ⊆
      H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro t ht
    exact ⟨by linarith [ht.1, epochStart_ge_initial (p.i - 1)], ht.2⟩
  have hfloor := seedM15_path_scalar_lower P inputs.pinched H.spacetime path hwindow
  have htotalStart : tau + d ≤ T - surgeryEpochStart (p.i - 1) := by
    linarith [htauWindow.2]
  have htotalTop : tau + d ≤ surgeryEpochStart (p.i + 1) :=
    htotalStart.trans (hStime.trans hThi)
  have hinterior : T - (tau + d) ∈ interior H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    change T - (tau + d) ∈ interior (Icc (0 : ℝ) T)
    rw [interior_Icc]
    constructor
    · linarith [epochStart_ge_initial (p.i - 1)]
    · linarith
  refine ⟨by linarith, htotalStart, htotalTop, hinterior, ?_⟩
  exact seed_image_comparisons P P44 p inputs.old inputs.pinched H.spacetime hB path hmin
    htau htauS (hStime.trans hThi) htotalTop hfloor hshort htold htime htime0 y0 x0 rfl
    hpoint hpositive e hbase hscalar hRm

end PoincareConjecture.M47
