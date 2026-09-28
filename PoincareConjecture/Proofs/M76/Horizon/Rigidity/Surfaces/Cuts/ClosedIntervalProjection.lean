import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.OriginalTriangleCopies

theorem strictMonoOn_Icc_of_strictMonoOn_Ioo
    {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (hm : StrictMonoOn f (Ioo a b)) : StrictMonoOn f (Icc a b) := by
  intro x hx y hy hxy
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  obtain ⟨v, huv, hvy⟩ := exists_between huy
  have hu : u ∈ Ioo a b := ⟨hx.1.trans_lt hxu, huy.trans_le hy.2⟩
  have hv : v ∈ Ioo a b := ⟨hu.1.trans huv, hvy.trans_le hy.2⟩
  have hleft : f x ≤ f u := by
    apply ContinuousWithinAt.closure_le (s := Ioo x u)
    · rw [closure_Ioo hxu.ne]
      exact ⟨le_rfl, hxu.le⟩
    · exact (hc x hx).mono (fun z hz ↦
        ⟨hx.1.trans hz.1.le, hz.2.le.trans hu.2.le⟩)
    · exact continuousWithinAt_const
    · intro z hz
      exact (hm ⟨hx.1.trans_lt hz.1, hz.2.trans hu.2⟩ hu hz.2).le
  have hright : f v ≤ f y := by
    apply ContinuousWithinAt.closure_le (f := fun _ ↦ f v) (g := f) (x := y)
      (s := Ioo v y)
    · rw [closure_Ioo hvy.ne]
      exact ⟨hvy.le, le_rfl⟩
    · exact continuousWithinAt_const
    · exact (hc y hy).mono (fun z hz ↦
        ⟨hv.1.le.trans hz.1.le, hz.2.le.trans hy.2⟩)
    · intro z hz
      exact (hm hv ⟨hv.1.trans hz.1, hz.2.trans_le hy.2⟩ hz.1).le
  exact hleft.trans_lt ((hm hu hv huv).trans_le hright)

theorem injOn_Icc_of_injOn_Ioo
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hi : InjOn f (Ioo a b)) :
    InjOn f (Icc a b) := by
  rcases (hc.mono Ioo_subset_Icc_self).strictMonoOn_of_injOn_Ioo hab hi with hm | hm
  · exact (strictMonoOn_Icc_of_strictMonoOn_Ioo hc hm).injOn
  · have hn : StrictMonoOn (fun x ↦ -f x) (Ioo a b) := by
      intro x hx y hy hxy
      exact neg_lt_neg (hm hx hy hxy)
    have hni := (strictMonoOn_Icc_of_strictMonoOn_Ioo hc.neg hn).injOn
    intro x hx y hy hxy
    exact hni hx hy (congrArg Neg.neg hxy)

end PoincareConjecture.M76.OriginalTriangleCopies
