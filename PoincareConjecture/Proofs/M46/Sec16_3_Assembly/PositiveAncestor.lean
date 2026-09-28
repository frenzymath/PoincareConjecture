import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveHistoryPaths









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M46



theorem positiveAncestorExclusion
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D) :
    PositiveAncestorExclusion H := by
  intro tau htau ht y hpath hpositive
  obtain ⟨path⟩ := hpath
  let γ : ℝ → H.spacetime.history.generalized.point := fun s => path.curve (tau - s)
  have hmaps : MapsTo (fun s : ℝ => tau - s) (Icc 0 tau) (Icc 0 tau) := by
    intro s hs
    exact ⟨sub_nonneg.mpr hs.2, sub_le_self _ hs.1⟩
  have hγ : ContinuousOn γ (Icc 0 tau) := path.curve_continuous.comp
    (continuous_const.sub continuous_id).continuousOn hmaps
  have hclock : MonotoneOn (fun s => (γ s).1) (Icc 0 tau) := by
    intro s hs t ht' hst
    have hs' := path.curve_time (tau - s) (hmaps hs)
    have ht'' := path.curve_time (tau - t) (hmaps ht')
    change (γ s).1 = D.time - (tau - s) at hs'
    change (γ t).1 = D.time - (tau - t) at ht''
    change (γ s).1 ≤ (γ t).1
    rw [hs', ht'']
    linarith
  have hfirst : γ 0 = (⟨D.time - tau, y⟩ : H.spacetime.history.generalized.point) := by
    change path.curve (tau - 0) = _
    rw [sub_zero, path.curve_end]
    exact (H.spacetime.geometry.sliceIdentification (D.time - tau)).identification_eq y
  have hlast : γ tau = (⟨D.time, H.center⟩ : H.spacetime.history.generalized.point) := by
    change path.curve (tau - tau) = _
    rw [sub_self, path.curve_start]
    exact (H.spacetime.geometry.sliceIdentification D.time).identification_eq H.center
  have hstart : HistoryPositive H.spacetime.history.history (γ 0) := by
    rw [hfirst]
    intro ht'
    exact hpositive
  have hend := historyPositive_along_path H.spacetime.history.history htau.le γ hγ hclock hstart
  rw [hlast] at hend
  have hpos := hend H.time_mem
  apply D.not_positive
  simpa only [H.center_eq] using hpos

end PoincareConjecture.Proofs.M46
