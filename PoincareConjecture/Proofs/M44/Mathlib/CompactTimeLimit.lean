import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Real
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Poincare

variable {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]




theorem continuousWithinAt_time_left_of_compact_uniform
    [ProperSpace X]
    {f : ℝ × X → Y} {U : Set X} {T : ℝ} (hU : IsOpen U)
    (hslice : ContinuousOn (fun x => f (T, x)) U)
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ U → ∀ eta : ℝ, 0 < eta →
      ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, T - d < t → t < T →
        ∀ x ∈ K, dist (f (t, x)) (f (T, x)) < eta)
    {x : X} (hx : x ∈ U) :
    ContinuousWithinAt f (Iic T ×ˢ U) (T, x) := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hhalf : 0 < r / 2 := half_pos hr
  have hK : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrU
  have hg0 : ContinuousAt (fun y : X => f (T, y)) x :=
    hslice.continuousAt (hU.mem_nhds hx)
  have hg : ContinuousAt (fun p : ℝ × X => f (T, p.2)) (T, x) :=
    ContinuousAt.comp (f := fun p : ℝ × X => p.2)
      (g := fun y : X => f (T, y)) (x := (T, x)) hg0 continuous_snd.continuousAt
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨d, hd, hbound⟩ := hlim (closedBall x (r / 2)) (isCompact_closedBall _ _) hK
    (eta / 2) (half_pos heta)
  have htnear : {p : ℝ × X | T - d < p.1} ∈ 𝓝 (T, x) :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (sub_lt_self T hd))
  have hxnear : {p : ℝ × X | p.2 ∈ ball x (r / 2)} ∈ 𝓝 (T, x) :=
    continuous_snd.continuousAt.preimage_mem_nhds (ball_mem_nhds x hhalf)
  have hgnear : ∀ᶠ p in 𝓝 (T, x), dist (f (T, p.2)) (f (T, x)) < eta / 2 :=
    Metric.tendsto_nhds.mp hg (eta / 2) (half_pos heta)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds htnear,
    mem_nhdsWithin_of_mem_nhds hxnear, hgnear.filter_mono nhdsWithin_le_nhds]
      with p hp htp hxp hgp
  rcases lt_or_eq_of_le (show p.1 ≤ T from hp.1) with hlt | heq
  · exact (dist_triangle (f p) (f (T, p.2)) (f (T, x))).trans_lt
      (by
        have h := hbound p.1 htp hlt p.2 (ball_subset_closedBall hxp)
        linarith)
  · calc
      dist (f p) (f (T, x)) = dist (f (T, p.2)) (f (T, x)) :=
        congrArg (fun z => dist (f z) (f (T, x))) (Prod.ext heq rfl)
      _ < eta := hgp.trans (half_lt_self heta)




theorem continuousAt_of_time_sides
    {f : ℝ × X → Y} {U : Set X} {T : ℝ} {x : X}
    (hU : IsOpen U) (hx : x ∈ U)
    (hleft : ContinuousWithinAt f (Iic T ×ˢ U) (T, x))
    (hright : ContinuousWithinAt f (Ici T ×ˢ U) (T, x)) :
    ContinuousAt f (T, x) := by
  have h := hleft.union hright
  rw [← union_prod, Iic_union_Ici] at h
  exact h.continuousAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hx⟩)




theorem continuousOn_time_of_compact_uniform
    [ProperSpace X] {f : ℝ × X → Y} {U : Set X} {a T b : ℝ}
    (hU : IsOpen U) (hTb : T < b)
    (hleft : ContinuousOn f (Ioo a T ×ˢ U))
    (hright : ContinuousOn f (Ico T b ×ˢ U))
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ U → ∀ eta : ℝ, 0 < eta →
      ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, T - d < t → t < T →
        ∀ x ∈ K, dist (f (t, x)) (f (T, x)) < eta) :
    ContinuousOn f (Ioo a b ×ˢ U) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  apply ContinuousAt.continuousWithinAt
  rcases lt_trichotomy t T with hlt | heq | hgt
  · exact hleft.continuousAt ((isOpen_Ioo.prod hU).mem_nhds ⟨⟨ht.1, hlt⟩, hx⟩)
  · subst t
    apply continuousAt_of_time_sides hU hx
    · apply continuousWithinAt_time_left_of_compact_uniform hU _ hlim hx
      exact hright.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy => ⟨⟨le_rfl, hTb⟩, hy⟩)
    · apply (hright ⟨T, x⟩ ⟨⟨le_rfl, hTb⟩, hx⟩).mono_of_mem_nhdsWithin
      have hnear : {p : ℝ × X | p.1 < b} ∈ 𝓝 (T, x) :=
        continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hTb)
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnear]
        with p hp hpb
      exact ⟨⟨hp.1, hpb⟩, hp.2⟩
  · apply (hright.mono (prod_mono Ioo_subset_Ico_self Subset.rfl)).continuousAt
    exact (isOpen_Ioo.prod hU).mem_nhds ⟨⟨hgt, ht.2⟩, hx⟩

end Poincare
