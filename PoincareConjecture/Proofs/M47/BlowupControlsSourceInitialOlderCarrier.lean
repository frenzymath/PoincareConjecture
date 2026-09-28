import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialAxialCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem source_initial_older_carrier_geometry
    {F : SurgeryFlowData.{u}} {t : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {A r W : ℝ} (initial : SurgeryCapInitialComparison F t hT i A)
    (hr : 0 < r) (hW : 0 < W) (hA : r + 2 < A)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 r)
    (havoid : initial.chart x ∉ ((F.event t hT).caps i).carrier)
    (hmargin : (((F.event t hT).necks i).neck.coordinate_inverse
      (sourceInitialOldMap initial x)).2 + W < 0)
    (hdelta : 4 * r + W + 4 < ((F.event t hT).necks i).neck.epsilon⁻¹) :
    let N := ((F.event t hT).necks i).neck
    let y := sourceInitialOldMap initial x
    let c := (N.coordinate_inverse y).2
    let R := 4 * r + W + 3
    let V := N.region (c - W) (c + W)
    IsOpen V ∧ y ∈ V ∧ V.Nonempty ∧
      V ⊆ N.region (-N.epsilon⁻¹) 0 ∧ V ⊆ N.region (-R) R := by
  let N := ((F.event t hT).necks i).neck
  let y := sourceInitialOldMap initial x
  let c := (N.coordinate_inverse y).2
  let R := 4 * r + W + 3
  let V := N.region (c - W) (c + W)
  have hxA : x ∈ F.standard_initial.metric.ball 0 A :=
    hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hA]))
  have hy : y ∈ N.region (-N.epsilon⁻¹) 0 :=
    (source_initial_chart_retention hT i initial hxA havoid).2.2
  have hheight : |c| < 4 * r := source_initial_old_map_height_lt hT i initial hr hA hx havoid
  have hends := abs_lt.mp hheight
  have hyV : y ∈ V := ⟨hy.1, by dsimp only [c]; constructor <;> linarith only [hW]⟩
  refine ⟨M36.neck_region_isOpen N _ _, hyV, ⟨y, hyV⟩, ?_, ?_⟩
  · intro p hp
    refine ⟨hp.1, ?_, hp.2.2.trans hmargin⟩
    change -N.epsilon⁻¹ < (N.coordinate_inverse p).2
    have hlo : -N.epsilon⁻¹ < c - W := by linarith only [hends.1, hdelta]
    exact hlo.trans hp.2.1
  · intro p hp
    refine ⟨hp.1, ?_, ?_⟩
    · change -R < (N.coordinate_inverse p).2
      have hlo : -R < c - W := by dsimp only [R]; linarith only [hends.1]
      exact hlo.trans hp.2.1
    · change (N.coordinate_inverse p).2 < R
      have hhi : c + W < R := by dsimp only [R]; linarith only [hends.2]
      exact hp.2.2.trans hhi

end PoincareConjecture.M47
