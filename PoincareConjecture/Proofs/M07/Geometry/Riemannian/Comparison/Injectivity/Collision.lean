import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture

variable {E X : Type*} [TopologicalSpace E] [T2Space E]
  [TopologicalSpace X] [T2Space X]

theorem isCompact_colliding_pairs {K : Set E} (hK : IsCompact K) {f : E → X}
    (hf : ContinuousOn f K)
    (hinj : ∀ x ∈ K, ∃ U ∈ 𝓝 x, InjOn f U) :
    IsCompact {z : E × E | z.1 ∈ K ∧ z.2 ∈ K ∧ f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  let S : Set (E × E) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ f z.1 = f z.2 ∧ z.1 ≠ z.2}
  have hsub : S ⊆ K ×ˢ K := fun _ h => ⟨h.1, h.2.1⟩
  have hclosedEq : IsClosed {z : E × E | z ∈ K ×ˢ K ∧ f z.1 = f z.2} :=
    (hK.prod hK).isClosed.isClosed_eq
      (hf.comp continuous_fst.continuousOn (fun _ h => h.1))
      (hf.comp continuous_snd.continuousOn (fun _ h => h.2))
  have hclosure : closure S ⊆ S := by
    intro z hz
    have hsubEq : S ⊆ {z : E × E | z ∈ K ×ˢ K ∧ f z.1 = f z.2} :=
      fun _ h => ⟨hsub h, h.2.2.1⟩
    have hzEq := closure_minimal hsubEq hclosedEq hz
    refine ⟨hzEq.1.1, hzEq.1.2, hzEq.2, ?_⟩
    intro hdiag
    obtain ⟨U, hU, hUi⟩ := hinj z.1 hzEq.1.1
    have hU' : U ∈ 𝓝 z.2 := hdiag ▸ hU
    have hprod : U ×ˢ U ∈ 𝓝 z := by
      rw [nhds_prod_eq]
      exact prod_mem_prod hU hU'
    obtain ⟨w, hwU, hwS⟩ := mem_closure_iff_nhds.mp hz _ hprod
    exact hwS.2.2.2 (hUi hwU.1 hwU.2 hwS.2.2.1)
  have hSclosed : IsClosed S := isClosed_of_closure_subset hclosure
  exact (hK.prod hK).of_isClosed_subset hSclosed hsub

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_minimal_collision {f : F → X} {r : ℝ}
    (hf : ContinuousOn f (Metric.closedBall 0 r))
    (hinj : ∀ x ∈ Metric.closedBall 0 r, ∃ U ∈ 𝓝 x, InjOn f U)
    (hnot : ¬ InjOn f (Metric.closedBall 0 r)) :
    ∃ v ∈ Metric.closedBall 0 r, ∃ w ∈ Metric.closedBall 0 r,
      f v = f w ∧ v ≠ w ∧ 0 < max ‖v‖ ‖w‖ ∧
      ∀ x ∈ Metric.closedBall 0 r, ∀ y ∈ Metric.closedBall 0 r,
        f x = f y → x ≠ y → max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖ := by
  let S : Set (F × F) := {z | z.1 ∈ Metric.closedBall 0 r ∧
    z.2 ∈ Metric.closedBall 0 r ∧ f z.1 = f z.2 ∧ z.1 ≠ z.2}
  have hS : IsCompact S := isCompact_colliding_pairs (isCompact_closedBall 0 r) hf hinj
  have hSne : S.Nonempty := by
    simp only [InjOn, not_forall] at hnot
    obtain ⟨v, hv, w, hw, heq, hne⟩ := hnot
    exact ⟨(v, w), hv, hw, heq, hne⟩
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hSne
    (show ContinuousOn (fun z : F × F => max ‖z.1‖ ‖z.2‖) S from
      (continuous_fst.norm.max continuous_snd.norm).continuousOn)
  refine ⟨z.1, hz.1, z.2, hz.2.1, hz.2.2.1, hz.2.2.2, ?_, ?_⟩
  · by_contra hpos
    have hzero : max ‖z.1‖ ‖z.2‖ ≤ 0 := le_of_not_gt hpos
    have hv : z.1 = 0 := norm_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hzero) (norm_nonneg _))
    have hw : z.2 = 0 := norm_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hzero) (norm_nonneg _))
    exact hz.2.2.2 (hv.trans hw.symm)
  · intro x hx y hy heq hne
    exact hmin (show (x, y) ∈ S from ⟨hx, hy, heq, hne⟩)

end Normed

section EqualRadius

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [T2Space X] in

private theorem not_norm_lt_of_minimal_collision
    {f : F → X} {r : ℝ} {v w : F}
    (hv : ‖v‖ ≤ r) (hwv : ‖w‖ < ‖v‖) (heq : f v = f w) (hne : v ≠ w)
    (hf : ContinuousAt f v)
    (e : OpenPartialHomeomorph F X) (hw : w ∈ e.source)
    (he : EqOn f e e.source)
    (hmin : ∀ x ∈ Metric.closedBall 0 r, ∀ y ∈ Metric.closedBall 0 r,
      f x = f y → x ≠ y → max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) : False := by
  obtain ⟨U, V, hU, hV, hvU, hwV, hdisj⟩ := t2_separation hne
  let W := V ∩ e.source ∩ Metric.ball (0 : F) ‖v‖
  have hwW : w ∈ W := ⟨⟨hwV, hw⟩, by simpa only [Metric.mem_ball, dist_zero_right] using hwv⟩
  have hW : IsOpen W := (hV.inter e.open_source).inter Metric.isOpen_ball
  have hpre : ∀ᶠ x in 𝓝 v, f x ∈ e '' W := by
    apply hf.preimage_mem_nhds
    rw [heq, he hw]
    exact e.image_mem_nhds hw (hW.mem_nhds hwW)
  have hnear : ∀ᶠ t : ℝ in 𝓝 1, t • v ∈ U ∧ f (t • v) ∈ e '' W := by
    have ht : Tendsto (fun t : ℝ => t • v) (𝓝 1) (𝓝 v) := by
      simpa only [ContinuousAt, one_smul] using
        (show Continuous (fun t : ℝ => t • v) by fun_prop).continuousAt (x := 1)
    exact ht (inter_mem (hU.mem_nhds hvU) hpre)
  obtain ⟨a, b, h1ab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let t : ℝ := (max a 0 + 1) / 2
  have ht0 : 0 ≤ t := by dsimp [t]; have := le_max_right a 0; linarith
  have ht1 : t < 1 := by dsimp [t]; have : max a 0 < 1 := max_lt h1ab.1 zero_lt_one; linarith
  have hat : a < t := by dsimp [t]; have := le_max_left a 0; linarith [h1ab.1]
  obtain ⟨htU, y, hyW, hy⟩ := hab ⟨hat, ht1.trans h1ab.2⟩
  have hvpos : 0 < ‖v‖ := (norm_nonneg w).trans_lt hwv
  have htv : ‖t • v‖ < ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht0]
    exact (mul_lt_mul_of_pos_right ht1 hvpos).trans_eq (one_mul _)
  have hyv : ‖y‖ < ‖v‖ := by simpa only [Metric.mem_ball, dist_zero_right] using hyW.2
  have hty : t • v ≠ y := by
    intro h
    exact Set.disjoint_left.mp hdisj htU (h.symm ▸ hyW.1.1)
  have hbound := hmin (t • v)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using htv.le.trans hv)
    y (by simpa only [Metric.mem_closedBall, dist_zero_right] using hyv.le.trans hv)
    (hy.symm.trans (he hyW.1.2).symm) hty
  exact (not_lt_of_ge hbound) ((max_lt htv hyv).trans_le (le_max_left _ _))

omit [T2Space X] in

theorem norm_eq_of_minimal_collision
    {f : F → X} {r : ℝ} {v w : F}
    (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) (heq : f v = f w) (hne : v ≠ w)
    (hfv : ContinuousAt f v) (hfw : ContinuousAt f w)
    (ev ew : OpenPartialHomeomorph F X) (hvs : v ∈ ev.source) (hws : w ∈ ew.source)
    (hev : EqOn f ev ev.source) (hew : EqOn f ew ew.source)
    (hmin : ∀ x ∈ Metric.closedBall 0 r, ∀ y ∈ Metric.closedBall 0 r,
      f x = f y → x ≠ y → max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) : ‖v‖ = ‖w‖ := by
  apply le_antisymm
  · by_contra h
    exact not_norm_lt_of_minimal_collision hv (lt_of_not_ge h) heq hne hfv ew hws hew hmin
  · by_contra h
    apply not_norm_lt_of_minimal_collision hw (lt_of_not_ge h) heq.symm hne.symm
      hfw ev hvs hev
    simpa only [max_comm ‖w‖ ‖v‖] using hmin

omit [T2Space X] [NormedSpace ℝ F] in

theorem isLocalMin_max_inverse_norm_of_minimal_collision
    {f : F → X} {r : ℝ} {v w : F}
    (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) (heq : f v = f w) (hne : v ≠ w)
    (ev ew : OpenPartialHomeomorph F X) (hvs : v ∈ ev.source) (hws : w ∈ ew.source)
    (hev : EqOn f ev ev.source) (hew : EqOn f ew ew.source)
    (hmin : ∀ x ∈ Metric.closedBall 0 r, ∀ y ∈ Metric.closedBall 0 r,
      f x = f y → x ≠ y → max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) :
    IsLocalMin (fun q => max ‖ev.symm q‖ ‖ew.symm q‖) (f v) := by
  have hvt : f v ∈ ev.target := (hev hvs).symm ▸ ev.map_source hvs
  have hwt : f v ∈ ew.target := heq.symm ▸ (hew hws).symm ▸ ew.map_source hws
  have hiv : ev.symm (f v) = v := by rw [hev hvs, ev.left_inv hvs]
  have hiw : ew.symm (f v) = w := by rw [heq, hew hws, ew.left_inv hws]
  have hnear : ∀ᶠ q in 𝓝 (f v), ev.symm q ≠ ew.symm q :=
    ((ev.continuousAt_symm hvt).ne_iff_eventually_ne
      (ew.continuousAt_symm hwt)).mp (by rwa [hiv, hiw])
  change ∀ᶠ q in 𝓝 (f v), max ‖ev.symm (f v)‖ ‖ew.symm (f v)‖ ≤ _
  rw [hiv, hiw]
  filter_upwards [hnear, ev.open_target.mem_nhds hvt, ew.open_target.mem_nhds hwt]
    with q hne' hqv hqw
  by_cases hvq : ‖ev.symm q‖ ≤ r
  · by_cases hwq : ‖ew.symm q‖ ≤ r
    · apply hmin (ev.symm q) (by simpa using hvq) (ew.symm q) (by simpa using hwq)
      · rw [hev (ev.map_target hqv), hew (ew.map_target hqw),
          ev.right_inv hqv, ew.right_inv hqw]
      · exact hne'
    · exact (max_le hv hw).trans ((le_of_not_ge hwq).trans (le_max_right _ _))
  · exact (max_le hv hw).trans ((le_of_not_ge hvq).trans (le_max_left _ _))

end EqualRadius

end PoincareConjecture
