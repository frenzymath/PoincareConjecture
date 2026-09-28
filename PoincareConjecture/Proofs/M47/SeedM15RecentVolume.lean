import PoincareConjecture.Proofs.M47.SeedM15RecentAncestry
import PoincareConjecture.Proofs.M47.SeedM15OldSeed
import PoincareConjecture.Proofs.M47.SeedM15SeedVolume
import PoincareConjecture.Proofs.M47.SeedM15Attainment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem seedM15_recent_volume_of_confinement
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p) {B c rNext cutoff Delta1 : ℝ}
    (hB : 1 ≤ B) (hBanalytic : seedAnalyticConstant S ≤ B) (hc : 0 < c)
    (hrNext : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoff : cutoff ≤ capScalarCutoff p.setup.epsilon c rNext)
    (hDelta : Delta1 ≤ surgeryEpochStart (p.i - 1) / 2)
    (uniform : M15GeneralizedUniformData.{u} 3 (surgeryEpochStart (p.i + 1))
      (actionBudget p / (4 * p.setup.epsilon))
      (p.kappa (Fin.last p.i) * seedImageRadius B (p.r (Fin.last p.i)) ^ 3 / 8))
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain} {x : (F.slice T).carrier}
    (H : SeedM15TestHistory T hT hTF x r) (hTO : T ∈ surgeryObservationInterval O)
    (hTlo : surgeryEpochStart p.i ≤ T) (hr : 0 < r) (hrEps : r ≤ p.setup.epsilon)
    (confinement : ActionConfinement H.spacetime.geometry.toLGeometry T
      (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val)
    (hbarrier : confinement.barrier = actionBudget p)
    {a b : ℝ} (hb : b ∈ Icc (-T) 0) (ha : a ∈ Icc b 0)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hU : (U : Set (F.slice T).carrier) = connectedComponent x)
    (hcompact : IsCompact (U : Set (F.slice T).carrier))
    (hconnected : IsConnected (U : Set (F.slice T).carrier))
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (hbased : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hbirth : T + b / 1 = 0 ∨ ∃ hsurgery : T + b / 1 ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (T + b / 1)).carrier],
        ∃ i : Fin (F.event (T + b / 1) hsurgery).cap_count,
          (e.forward b ⟨le_rfl, hb.2⟩ '' (U : Set (F.slice T).carrier) ∩
            ((F.event (T + b / 1) hsurgery).caps i).carrier).Nonempty)
    (honset : a = b ∨ ∀ z : U,
      ¬ SurgeryPositiveComponentAt F (T + a / 1) (e.forward a ha z.val))
    (hrecent : surgeryEpochStart p.i - Delta1 / 2 < T + a / 1)
    (hbirthFloor : ∀ (s : ℝ) (hs : s ∈ F.surgery_times) [Nonempty (F.slice s).carrier],
      s ∈ surgeryObservationInterval O → surgeryEpochStart (p.i - 1) ≤ s →
      ∀ i : Fin (F.event s hs).cap_count, ∀ y ∈ ((F.event s hs).caps i).carrier,
        c / (2 * (F.parameters.h s) ^ 2) ≤ (F.connection s).scalarCurvature y) :
    ENNReal.ofReal ((uniform.kappa / 8) * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  have hstrip : Icc (surgeryEpochStart (p.i - 1)) T ⊆
      H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro s hs
    exact ⟨(by linarith [hs.1, epochStart_ge_initial (p.i - 1)]), hs.2⟩
  obtain ⟨region⟩ := seedM15_minimizingRegion P.m12 P.m14
    H.spacetime.geometry.toLGeometry
    ((H.spacetime.geometry.sliceIdentification T).identification H.center)
    confinement hstrip
  have hThi : T ≤ surgeryEpochStart (p.i + 1) := hTO.2.le.trans inputs.next_epoch.2
  obtain ⟨endpoint, path, hmin, hshort, tau, htauWindow, hmargin, hlow⟩ :=
    seedM15_lowScalarMinimizer P p inputs.pinched H hTlo hThi confinement region
  have htauEps : p.setup.epsilon ^ 2 ≤ tau :=
    (le_max_left _ _).trans htauWindow.1
  have htau : tau ∈ Ioc 0 (T - surgeryEpochStart (p.i - 1)) := by
    refine ⟨(sq_pos_of_pos p.setup.epsilon_pos).trans_le htauEps, ?_⟩
    linarith [htauWindow.2, sq_nonneg p.setup.epsilon]
  have hpoint0 : 0 ≤ T - tau := by
    linarith [htauWindow.2, sq_nonneg p.setup.epsilon, epochStart_ge_initial (p.i - 1)]
  have hbefore : T - tau < T + a / 1 :=
    seedM15_lowPoint_before_recent p hmargin hDelta hrecent
  have hnonpositive := seedM15_recent_path_nonpositive P.m04 inputs.terminal_policy
    H hTO hb ha U hU hcompact hconnected e hbased hbirth honset path htau hpoint0 hbefore
  have hbeforeTi : T - tau < surgeryEpochStart p.i := by
    linarith [epochStart_ge_initial (p.i - 1)]
  obtain ⟨hseedEps, hseedStart, hseedTop, hseedTime, A, hA, hne, hvolume, hpaths⟩ :=
    seedM15_oldSeed P P44 S p hp hB hBanalytic hc hrNext hrLast hcutoff inputs
      H hTO.2.le path hmin hshort htauWindow hbeforeTi hlow hnonpositive hbirthFloor
  exact seedM15_volume_of_oldSeed P p uniform H hr hrEps confinement hbarrier region
    hseedEps hseedStart hseedTop hseedTime A hA hne hvolume (fun q hq => by
      obtain ⟨comparison, hcomparison⟩ := hpaths q hq
      exact ⟨comparison, hcomparison.le⟩)

end PoincareConjecture.M47
