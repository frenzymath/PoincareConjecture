import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_CompactMinimizers
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_StableImage
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_EpochWindow
import PoincareConjecture.Proofs.M15.Thm8_10_StableSurvival
import PoincareConjecture.Proofs.M04

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

theorem stableSource_of_actual_seed_comparisons
    (P : M46Predecessors.{u}) {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) {D : NoncollapseTest F O} (history : HalfRadiusHistory D)
    (confinement : ActionConfinement history.spacetime.geometry.toLGeometry
      D.time (surgeryEpochStart (p.i - 1))
      ((history.spacetime.geometry.sliceIdentification D.time).identification history.center).val)
    (hbarrier : confinement.barrier = actionBudget p)
    (M : MinimizingRegion history.spacetime.geometry.toLGeometry
      D.time (surgeryEpochStart (p.i - 1))
      ((history.spacetime.geometry.sliceIdentification D.time).identification history.center).val
      confinement)
    {tau V : ℝ} (htau : p.setup.epsilon ^ 2 ≤ tau)
    (htauStart : tau ≤ D.time - surgeryEpochStart (p.i - 1))
    (htauTop : tau ≤ surgeryEpochStart (p.i + 1))
    (htime : D.time - tau ∈ interior history.spacetime.history.generalized.interval)
    (A : Set (history.spacetime.geometry.toLGeometry.slices (D.time - tau)).Point)
    (hA : IsOpen A) (hne : A.Nonempty)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume
      (history.spacetime.geometry.toLGeometry.slices (D.time - tau)).metricOnPoints A)
    (hpaths : ∀ q ∈ closure A,
      ∃ path : M14BackwardPath history.spacetime.geometry.toLGeometry D.time 0 tau
        ((history.spacetime.geometry.sliceIdentification D.time).identification history.center).val
        q.val,
        M14BackwardLAction history.spacetime.geometry.toLGeometry path ≤ actionBudget p / 2) :
    Nonempty (StableSource history (surgeryEpochStart (p.i + 1))
      (actionBudget p / (4 * p.setup.epsilon)) V) := by
  have htauPos : 0 < tau := (sq_pos_of_pos p.setup.epsilon_pos).trans_le htau
  generalize hb : Real.sqrt tau = b at *
  have hbpos : 0 < b := hb ▸ Real.sqrt_pos.mpr htauPos
  have hbsq : b ^ 2 = tau := by rw [← hb, Real.sq_sqrt htauPos.le]
  subst tau
  let G := history.spacetime.geometry.toLGeometry
  let x : G.Point :=
    ((history.spacetime.geometry.sliceIdentification D.time).identification history.center).val
  have hbase : G.spacetime.timeFunction x = D.time :=
    ((history.spacetime.geometry.sliceIdentification D.time).identification history.center).property
  have hHpos : 0 < surgeryEpochStart (p.i + 1) :=
    (by norm_num : (0 : ℝ) < 1 / 32).trans_le (epochStart_ge_initial _)
  have hLpos : 0 < actionBudget p := by unfold actionBudget; positivity
  have hbelow : actionBudget p / 2 < confinement.barrier := by rw [hbarrier]; linarith
  have hmin (q : (G.slices (D.time - b ^ 2)).Point) (hq : q ∈ closure A) :
      ∃ path : M14BackwardPath G D.time 0 (b ^ 2) x q.val, M14IsMinimizing path := by
    obtain ⟨competitor, hcompetitor⟩ := hpaths q hq
    have hclock : G.spacetime.timeFunction q.val = D.time - b ^ 2 := q.property
    have hback : D.time - G.spacetime.timeFunction q.val = b ^ 2 := by rw [hclock]; ring
    have hregion : q.val ∈ M.region := by
      apply (M.region_exact q.val).mpr
      refine ⟨?_, ?_⟩
      · rw [hclock]
        exact ⟨by linarith, by linarith⟩
      · rw [hback]
        exact ⟨competitor, hcompetitor.trans_lt hbelow⟩
    have h := M.minimizing q.val hregion
    rwa [hback] at h
  have haction (q : (G.slices (D.time - b ^ 2)).Point) (hq : q ∈ closure A)
      (path : M14BackwardPath G D.time 0 (b ^ 2) x q.val) (hpath : M14IsMinimizing path) :
      M14BackwardLAction G path ≤ actionBudget p / 2 := by
    obtain ⟨competitor, hcompetitor⟩ := hpaths q hq
    exact (hpath competitor).trans hcompetitor
  obtain ⟨LG⟩ := P.m14.conclusion _ _ _ G
  obtain ⟨E⟩ := LG.exponential.family D.time x hbase
  obtain ⟨q0, hq0⟩ := hne
  obtain ⟨m0, hm0⟩ := hmin q0 (subset_closure hq0)
  obtain ⟨stable⟩ := M15.exists_stableSet_of_minimizing LG E m0 hm0
  have hconf (Z : G.Horizontal x) (hZ : (Z, b) ∈ E.domain)
      (hZaction : E.action Z b ≤ actionBudget p / 2) :
      MapsTo (E.gamma Z) (Icc 0 b) confinement.cage := by
    let path := E.path Z b hZ hbpos
    have hpathAction : M14BackwardLAction G path < confinement.barrier := by
      rw [← E.action_eq Z b hZ hbpos]
      exact hZaction.trans_lt hbelow
    have htrace := confinement.paths_mem (b ^ 2) htauPos htauStart
      (E.gamma Z b) path hpathAction
    intro s hs
    have hsq : s ^ 2 ∈ Icc 0 (b ^ 2) :=
      ⟨sq_nonneg s, (sq_le_sq₀ hs.1 hbpos.le).mpr hs.2⟩
    have heq := E.path_coherent Z b hZ hbpos (s ^ 2) hsq
    rw [Real.sqrt_sq hs.1] at heq
    rw [← heq]
    exact htrace hsq
  have hnull := stable_image_full_measure_of_confined_actions ricciFlowCurvatureTheory.{0}
    P.m12 LG E hbpos stable q0 htime hA hmin (by positivity : 0 ≤ actionBudget p / 2)
    haction confinement.cage_compact hconf
  have hlength (q : (G.slices (D.time - b ^ 2)).Point) (hq : q ∈ A) :
      M14ReducedLengthValue G D.time 0 (b ^ 2) x q.val ≤
        actionBudget p / (4 * p.setup.epsilon) := by
    obtain ⟨path, hpath⟩ := hmin q (subset_closure hq)
    apply reducedLength_le_of_action_bound p.setup.epsilon_pos hLpos.le htau
    rw [← M14.action_eq_actionValue_of_minimizing path hpath]
    exact haction q (subset_closure hq) path hpath
  have hradius : (D.radius / 2) ^ 2 ≤ b ^ 2 := by
    have hrle : D.radius ≤ p.setup.epsilon := old.epsilon_eq ▸ D.radius_le
    nlinarith [D.radius_pos, p.setup.epsilon_pos]
  exact stableSource_of_comparison history E stable htauTop hradius
    (interior_subset htime) A hA hlength hvolume hnull

end PoincareConjecture.Proofs.M46
