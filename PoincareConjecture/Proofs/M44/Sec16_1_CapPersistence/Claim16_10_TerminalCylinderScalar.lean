import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c : ℝ} {U : Set C.carrier}

theorem cylinderTerminalChart_scalar_le
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale)) {x : C.carrier} (hx : x ∈ U)
    {K : ℝ} (hbound : ∀ s (hs : s ∈ Ico (0 : ℝ) c),
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K) :
    (F.event (origin + c / scale) hT).limit_connection.scalarCurvature
      (cylinderTerminalChart e hU hT r hr hr' x) ≤ K := by
  let event := F.event (origin + c / scale) hT
  let q := (event.pre_identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)
  have hq : q ∈ event.regular_limit :=
    cylinder_preterminal_mem_regular_limit P hpinch e hT r hr hr' hx ⟨K, hbound⟩
  change event.limit_connection.scalarCurvature (event.limit_identify.map q) ≤ K
  apply terminal_scalar_le_of_preterminal event hq
  filter_upwards [Ioo_mem_nhdsLT hr'.2] with t ht
  let s := scale * (t - origin)
  have hclock : origin + s / scale = t := by
    dsimp [s]
    field_simp [e.scale_pos.ne']
    ring
  have hrs : r < s := by
    have hrt : r / scale < t - origin := by linarith only [ht.1]
    simpa only [s, mul_comm] using (div_lt_iff₀ e.scale_pos).mp hrt
  have hsc : s < c := by
    have htc : t - origin < c / scale := by linarith only [ht.2]
    simpa only [s, mul_comm] using (lt_div_iff₀ e.scale_pos).mp htc
  have hs : s ∈ Ico (0 : ℝ) c := ⟨hr.1.trans hrs.le, hsc⟩
  have hs' : origin + s / scale ∈ Ico event.tMinus (origin + c / scale) := by
    rw [hclock]
    exact ⟨hr'.1.trans ht.1.le, ht.2⟩
  have hfixed := cylinder_preterminal_coordinates_eq_of_pinched P hpinch e hT
    s hs r hr hs' hr' x hx
  let y := (event.pre_identify ⟨origin + s / scale, hs'⟩).symm (e.forward s hs x)
  have hhom : MetricHomothety (event.pre_flow.metric (origin + s / scale))
      (F.metric (origin + s / scale)) (event.pre_identify ⟨origin + s / scale, hs'⟩) 1 := by
    intro z v w
    simpa only [one_mul] using event.pre_metric ⟨origin + s / scale, hs'⟩ z v w
  have heq := M13.homothety_scalarCurvature_eq _ _ _ 1 zero_lt_one hhom
    (event.pre_flow.connection (origin + s / scale)) (F.connection (origin + s / scale)) y
  dsimp only [y] at heq
  rw [Diffeomorph.apply_symm_apply, div_one, hfixed] at heq
  have hle : (event.pre_flow.connection (origin + s / scale)).scalarCurvature q ≤ K :=
    heq.symm.trans_le (hbound s hs)
  rwa [hclock] at hle

end PoincareConjecture.M44
