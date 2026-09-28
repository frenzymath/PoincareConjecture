import PoincareConjecture.Proofs.M47.SeedM15CapBox
import PoincareConjecture.Proofs.M47.SeedM15PathBox
import PoincareConjecture.Proofs.M47.SeedM15PathPositivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem seedM15_terminal_cap_path_nonpositive
    (hC : RicciFlowCurvatureTheory.{u})
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (R : M46RegularSpacetimeData W)
    {J : Set ℝ} (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T S : ℝ} (hTJ : T ∈ J) (hSurgery : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (hT : T ∈ R.history.generalized.interval)
    (center : (R.history.generalized.slice T).carrier)
    {i : Fin (F.event T hSurgery).cap_count}
    (hcontact : (connectedComponent (R.history.history.forward T hT center) ∩
      ((F.event T hSurgery).caps i).carrier).Nonempty)
    {endpoint : R.geometry.toLGeometry.Point}
    (path : M14BackwardPath R.geometry.toLGeometry T 0 S
      ((R.geometry.sliceIdentification T).identification center).val endpoint)
    {tau : ℝ} (htau : tau ∈ Ioc 0 S) :
    ¬ HistoryPositive R.history.history (path.curve tau) := by
  intro hpositive
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
  have hTmem : T ∈ Icc (T - tau) T := ⟨by linarith [htau.1], le_rfl⟩
  obtain ⟨q, x, hTbox, hpoint, _⟩ := seedM15_path_component_box
    R.history.generalized gamma hcont hTmem (hclock T hTmem)
  have hterminal : gamma T = (⟨T, center⟩ : R.history.generalized.point) := by
    change path.curve (T - T) = _
    rw [sub_self, path.curve_start]
    exact (R.geometry.sliceIdentification T).identification_eq center
  have hx : (R.history.generalized.box q).forward T hTbox x = center := by
    exact eq_of_heq (Sigma.mk.inj (hpoint.symm.trans hterminal)).2
  have hboxContact : (connectedComponent
      (R.history.history.forward T (m33BoxIntervalSubset R.history.generalized q hTbox)
        ((R.history.generalized.box q).forward T hTbox x)) ∩
      ((F.event T hSurgery).caps i).carrier).Nonempty := by
    rw [hx]
    exact hcontact
  have hmemT : gamma T ∈ componentBoxImage R.history.generalized ⟨q, x⟩ :=
    ⟨(⟨T, hTbox⟩, x), ⟨mem_univ _, mem_connectedComponent⟩, hpoint.symm⟩
  have hlim : Tendsto gamma (𝓝[<] T) (𝓝 (gamma T)) :=
    ((hcont T hTmem).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE (by linarith [htau.1] : T - tau < T))).mono Iio_subset_Iic_self
  have hnear : ∀ᶠ v in 𝓝[<] T, gamma v ∈
      componentBoxImage R.history.generalized ⟨q, x⟩ :=
    hlim ((componentBoxImage_isOpen R.history.generalized ⟨q, x⟩).mem_nhds hmemT)
  have hleft : max (T - tau) (F.event T hSurgery).tMinus < T :=
    max_lt (by linarith [htau.1]) (F.event T hSurgery).tMinus_lt
  have hnearLeft : ∀ᶠ v in 𝓝[<] T,
      v ∈ Ioo (max (T - tau) (F.event T hSurgery).tMinus) T := Ioo_mem_nhdsLT hleft
  obtain ⟨v, hv, hvimage⟩ := (hnearLeft.and hnear).exists
  have hvold : T - tau < v := (le_max_left _ _).trans_lt hv.1
  have hvpre : (F.event T hSurgery).tMinus < v := (le_max_right _ _).trans_lt hv.1
  have hvtime : v ∈ Icc (T - tau) T := ⟨hvold.le, hv.2.le⟩
  have hpv : HistoryPositive R.history.history (gamma v) :=
    seedM15_historyPositive_subpath R path (hmaps hvtime) ⟨htau.1.le, htau.2⟩
      (by linarith) hpositive
  obtain ⟨hvbox, hposv⟩ := seedM15_historyPositive_box_line_at R.history.history
    q x (hclock v hvtime) hvimage hpv
  exact seedM15_cap_child_box_nonpositive hC R.history.history hpolicy hTJ hSurgery
    q x hTbox ⟨v, ⟨hvpre.le, hv.2⟩⟩ hvbox hboxContact hposv

end PoincareConjecture.M47
