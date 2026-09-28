import PoincareConjecture.Proofs.M47.SeedM15CapBox
import PoincareConjecture.Proofs.M47.SeedM15PathBox
import PoincareConjecture.Proofs.M47.SeedM15PathPositivity
import PoincareConjecture.Proofs.M47.SeedM15ComponentCapture
import PoincareConjecture.Proofs.M47.SeedM15BoxImage
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem seedM15_birth_cap_path_nonpositive
    (hC : RicciFlowCurvatureTheory.{u})
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (R : M46RegularSpacetimeData W)
    {J : Set ℝ} (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T b S : ℝ} (hb : b < 0)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hcompact : IsCompact (U : Set (F.slice T).carrier))
    (hconnected : IsConnected (U : Set (F.slice T).carrier)) (x0 : U)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (hinterval : Icc (T + b) T ⊆ R.history.generalized.interval)
    (hbased : ∀ h z, z ∈ U → HEq (e.forward 0 h z) z)
    (hT : T ∈ R.history.generalized.interval)
    (center : (R.history.generalized.slice T).carrier)
    (hcenter : R.history.history.forward T hT center = x0.val)
    (hbirthJ : T + b / 1 ∈ J) (hbirth : T + b / 1 ∈ F.surgery_times)
    [Nonempty (F.slice (T + b / 1)).carrier]
    {i : Fin (F.event (T + b / 1) hbirth).cap_count}
    (hcontact : (connectedComponent (e.forward b ⟨le_rfl, hb.le⟩ x0.val) ∩
      ((F.event (T + b / 1) hbirth).caps i).carrier).Nonempty)
    {endpoint : R.geometry.toLGeometry.Point}
    (path : M14BackwardPath R.geometry.toLGeometry T 0 S
      ((R.geometry.sliceIdentification T).identification center).val endpoint)
    {tau : ℝ} (htau : tau ∈ Ioc 0 S) (hbefore : T - tau < T + b / 1) :
    ¬ HistoryPositive R.history.history (path.curve tau) := by
  intro hpositive
  let B := T + b / 1
  let E := F.event B hbirth
  have hBT : B < T := by dsimp [B]; simp only [div_one]; linarith
  let gamma : ℝ → R.history.generalized.point := fun t => path.curve (T - t)
  have hmaps : MapsTo (fun t : ℝ => T - t) (Icc (T - tau) T) (Icc 0 S) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1, htau.2]⟩
  have hcont : ContinuousOn gamma (Icc (T - tau) T) := path.curve_continuous.comp
    (continuous_const.sub continuous_id).continuousOn hmaps
  have hclock : ∀ t ∈ Icc (T - tau) T, (gamma t).1 = t := by
    intro t ht
    have h : (path.curve (T - t)).1 = T - (T - t) := path.curve_time (T - t) (hmaps ht)
    simpa only [gamma, sub_sub_cancel] using h
  have hBmem : B ∈ Icc (T - tau) T := ⟨hbefore.le, hBT.le⟩
  obtain ⟨q, x, hBbox, hpoint, _⟩ := seedM15_path_component_box
    R.history.generalized gamma hcont hBmem (hclock B hBmem)
  have hmemB : gamma B ∈ componentBoxImage R.history.generalized ⟨q, x⟩ :=
    ⟨(⟨B, hBbox⟩, x), ⟨mem_univ _, mem_connectedComponent⟩, hpoint.symm⟩
  have hcontB : ContinuousAt gamma B := (hcont B hBmem).continuousAt
    (Icc_mem_nhds hbefore hBT)
  have hnear : {t | gamma t ∈ componentBoxImage R.history.generalized ⟨q, x⟩} ∈ 𝓝 B :=
    hcontB ((componentBoxImage_isOpen R.history.generalized ⟨q, x⟩).mem_nhds hmemB)
  obtain ⟨l, r, ⟨hlB, hBr⟩, hbox⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  obtain ⟨v, hvlow, hvB⟩ := exists_between
    (max_lt hbefore (max_lt E.tMinus_lt hlB))
  have hvold : T - tau < v := (le_max_left _ _).trans_lt hvlow
  have hvpre : E.tMinus < v :=
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hvlow)
  have hlv : l < v := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hvlow)
  have hvtime : v ∈ Icc (T - tau) T := ⟨hvold.le, hvB.le.trans hBT.le⟩
  have hvimage : gamma v ∈ componentBoxImage R.history.generalized ⟨q, x⟩ :=
    hbox ⟨hlv, hvB.trans hBr⟩
  have hpv : HistoryPositive R.history.history (gamma v) :=
    seedM15_historyPositive_subpath R path (hmaps hvtime) ⟨htau.1.le, htau.2⟩
      (by linarith) hpositive
  obtain ⟨hvbox, hposv⟩ := seedM15_historyPositive_box_line_at R.history.history
    q x (hclock v hvtime) hvimage hpv
  obtain ⟨top, hBtop, _htopT, hfree⟩ := M44.exists_surgery_free_right_interval F
    (F.surgery_times_subset hbirth) hBT
  obtain ⟨w, hBw, hwtop⟩ := exists_between (lt_min hBr (lt_min hBT hBtop))
  have hwr : w < r := hwtop.trans_le (min_le_left _ _)
  have hwT : w < T := (hwtop.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hwfree : w < top := (hwtop.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hwtime : w ∈ Icc (T - tau) T := ⟨hbefore.le.trans hBw.le, hwT.le⟩
  have hwimage : gamma w ∈ componentBoxImage R.history.generalized ⟨q, x⟩ :=
    hbox ⟨hlB.trans hBw, hwr⟩
  have hwclock : (path.curve (T - w)).1 = w := hclock w hwtime
  have hwactual : (path.curve (T - w)).1 ∈ R.history.generalized.interval := by
    rw [hwclock]
    apply hinterval
    exact ⟨by simpa only [B, div_one] using hBw.le, hwT.le⟩
  have hwafter : b < -(T - w) := by
    change T + b / 1 < w at hBw
    simp only [div_one] at hBw
    linarith
  obtain ⟨s, hs, z, hsa, hphysical⟩ := seedM15_component_path_capture R U hcompact e
    hinterval hbased hT center x0 hcenter path (hmaps hwtime) hwafter hwactual
  have hsw : T + s / 1 = w := by rw [hsa]; ring
  have hsstrict : s ∈ Ioc b 0 := ⟨by rw [hsa]; exact hwafter, hs.2⟩
  obtain ⟨hsbox, hpost⟩ := seedM15_component_box_image R.history.history
    U hcompact hconnected e q x hwimage hs (hwclock.trans hsw.symm)
      hwactual z.property hphysical
  have hfreew : Disjoint F.surgery_times (Ioc B w) :=
    hfree.mono_right (Ioc_subset_Ioc le_rfl hwfree.le)
  have hfrees : Disjoint F.surgery_times (Ioc (T + b / 1) (T + s / 1)) := by
    simpa only [hsw] using hfreew
  exact seedM15_cap_birth_box_nonpositive hC R.history.history hpolicy U hcompact
    hconnected x0 e hb hbirthJ hbirth hcontact q x hBbox
      ⟨v, ⟨hvpre.le, hvB⟩⟩ hvbox hsstrict hsbox hfrees hpost hposv

end PoincareConjecture.M47
