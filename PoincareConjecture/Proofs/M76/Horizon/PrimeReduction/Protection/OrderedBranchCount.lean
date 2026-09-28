import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith









set_option autoImplicit false
open Set
open scoped Topology

namespace PoincareConjecture.M76

private theorem not_disjoint_positive_branch_images
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf1 : 0 < f 1) (hg1 : 0 < g 1) :
    ¬ Disjoint (f '' Ioc 0 1) (g '' Ioc 0 1) := by
  let y := min (f 1) (g 1) / 2
  have hy : 0 < y := half_pos (lt_min hf1 hg1)
  have hyf : y ≤ f 1 := (half_le_self (le_of_lt (lt_min hf1 hg1))).trans (min_le_left _ _)
  have hyg : y ≤ g 1 := (half_le_self (le_of_lt (lt_min hf1 hg1))).trans (min_le_right _ _)
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf
    (show y ∈ Icc (f 0) (f 1) by rw [hf0]; exact ⟨hy.le, hyf⟩)
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hg
    (show y ∈ Icc (g 0) (g 1) by rw [hg0]; exact ⟨hy.le, hyg⟩)
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (by
    intro h; have := hfs; rw [← h, hf0] at this; linarith)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro h; have := hgt; rw [← h, hg0] at this; linarith)
  intro hdis
  exact disjoint_left.mp hdis ⟨s, ⟨hspos, hs.2⟩, hfs⟩ ⟨t, ⟨htpos, ht.2⟩, hgt⟩

theorem card_le_two_of_disjoint_ordered_branches
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc 0 1))
    (hzero : ∀ i, f i 0 = 0) (hend : ∀ i, f i 1 ≠ 0)
    (hdis : Pairwise fun i j => Disjoint (f i '' Ioc 0 1) (f j '' Ioc 0 1)) :
    Fintype.card ι ≤ 2 := by
  classical
  let sign : ι → Bool := fun i => decide (0 < f i 1)
  have hinj : Function.Injective sign := by
    intro i j hij
    by_contra hne
    have hequiv : (0 < f i 1) ↔ (0 < f j 1) := by
      simpa only [sign, decide_eq_decide] using hij
    by_cases hi : 0 < f i 1
    · exact not_disjoint_positive_branch_images (hf i) (hf j) (hzero i) (hzero j)
        hi (hequiv.mp hi) (hdis hne)
    · have hj := mt hequiv.mpr hi
      have hi' : f i 1 < 0 := lt_of_le_of_ne (le_of_not_gt hi) (hend i)
      have hj' : f j 1 < 0 := lt_of_le_of_ne (le_of_not_gt hj) (hend j)
      have hneg : Disjoint ((fun t => -(f i t)) '' Ioc 0 1)
          ((fun t => -(f j t)) '' Ioc 0 1) := by
        apply disjoint_left.mpr
        rintro y ⟨s, hs, hsy⟩ ⟨t, ht, hty⟩
        exact disjoint_left.mp (hdis hne) ⟨s, hs, rfl⟩
          ⟨t, ht, neg_injective (hty.trans hsy.symm)⟩
      exact not_disjoint_positive_branch_images (hf i).neg (hf j).neg
        (by simp only [Pi.neg_apply, hzero i, neg_zero])
        (by simp only [Pi.neg_apply, hzero j, neg_zero])
        (neg_pos.mpr hi') (neg_pos.mpr hj') hneg
  simpa using Fintype.card_le_of_injective sign hinj

theorem card_le_two_of_disjoint_branches_in_real_chart
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (f : ι → ℝ → X) (p : X)
    (hf : ∀ i, ContinuousOn (f i) (Icc 0 1)) (hzero : ∀ i, f i 0 = p)
    (hpunct : ∀ i t, t ∈ Ioc 0 1 → f i t ≠ p)
    (hdis : Pairwise fun i j => Disjoint (f i '' Ioc 0 1) (f j '' Ioc 0 1))
    (q : OpenPartialHomeomorph X ℝ) (hp : p ∈ q.source) :
    Fintype.card ι ≤ 2 := by
  have hevent : ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] 0, ∀ i, f i t ∈ q.source := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hf i 0 (by simp)).preimage_mem_nhdsWithin
      (q.open_source.mem_nhds (by rw [hzero]; exact hp))
  obtain ⟨ε, hε, hεsource⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  let r := min (ε / 2) 1
  have hr : 0 < r := lt_min (half_pos hε) zero_lt_one
  have hr1 : r ≤ 1 := min_le_right _ _
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have htime {t : ℝ} (ht : t ∈ Icc 0 1) : r * t ∈ Icc 0 1 :=
    ⟨mul_nonneg hr.le ht.1, (mul_le_of_le_one_right hr.le ht.2).trans hr1⟩
  have htime' {t : ℝ} (ht : t ∈ Ioc 0 1) : r * t ∈ Ioc 0 1 :=
    ⟨mul_pos hr ht.1, (htime ⟨ht.1.le,ht.2⟩).2⟩
  have hsource (i : ι) {t : ℝ} (ht : t ∈ Icc 0 1) : f i (r * t) ∈ q.source := by
    apply hεsource ⟨?_, htime ht⟩ i
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (htime ht).1]
    exact lt_of_le_of_lt (mul_le_of_le_one_right hr.le ht.2) hrε
  let g : ι → ℝ → ℝ := fun i t => q (f i (r * t)) - q p
  apply card_le_two_of_disjoint_ordered_branches g
  · intro i
    exact (q.continuousOn.comp ((hf i).comp
      (continuous_const.mul continuous_id).continuousOn (fun _ ht => htime ht))
      (fun _ ht => hsource i ht)).sub continuousOn_const
  · intro i
    simp only [g, mul_zero, hzero, sub_self]
  · intro i h
    have heq : q (f i r) = q p := by simpa only [g, mul_one, sub_eq_zero] using h
    exact hpunct i r ⟨hr,hr1⟩ (q.injOn (by simpa using hsource i (show (1 : ℝ) ∈ Icc 0 1 by simp)) hp heq)
  · intro i j hij
    apply disjoint_left.mpr
    rintro y ⟨s, hs, hsy⟩ ⟨t, ht, hty⟩
    have heq : f i (r * s) = f j (r * t) := q.injOn
      (hsource i ⟨hs.1.le,hs.2⟩) (hsource j ⟨ht.1.le,ht.2⟩)
      (sub_left_injective (hsy.trans hty.symm))
    exact disjoint_left.mp (hdis hij) ⟨r*s,htime' hs,rfl⟩ ⟨r*t,htime' ht,heq.symm⟩

end PoincareConjecture.M76
