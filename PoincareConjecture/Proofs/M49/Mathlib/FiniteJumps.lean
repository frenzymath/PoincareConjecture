import Mathlib.Data.Finset.Max
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set Filter
open scoped Topology

theorem le_of_finite_left_jumps {β : Type*} [Preorder β] [TopologicalSpace β]
    [OrderClosedTopology β] {f : ℝ → β} {a b : ℝ} (S : Finset ℝ)
    (hab : a ≤ b) (hS : (S : Set ℝ) ⊆ Ioc a b)
    (hregular : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      Disjoint (S : Set ℝ) (Ioc x y) → f y ≤ f x)
    (hjump : ∀ T ∈ S, ∃ L, Tendsto f (𝓝[<] T) (𝓝 L) ∧ f T ≤ L) :
    f b ≤ f a := by
  classical
  induction S using Finset.induction_on_max generalizing a b with
  | empty =>
    exact hregular a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab (by simp)
  | insert T S hST ih =>
    have hT : T ∈ Ioc a b := hS (Finset.mem_insert_self T S)
    let c := (insert a S).max' (Finset.insert_nonempty a S)
    have hac : a ≤ c := (insert a S).le_max' a (Finset.mem_insert_self a S)
    have hzc (z : ℝ) (hz : z ∈ S) : z ≤ c :=
      (insert a S).le_max' z (Finset.mem_insert_of_mem hz)
    have hcT : c < T := ((insert a S).max'_lt_iff _).mpr (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hT.1
      · exact hST z hz)
    obtain ⟨L, hlim, hdrop⟩ := hjump T (Finset.mem_insert_self T S)
    have hL : L ≤ f a := by
      apply le_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsLT hcT] with t ht
      apply ih (hac.trans ht.1.le)
      · intro z hz
        exact ⟨(hS (Finset.mem_insert_of_mem hz)).1, (hzc z hz).trans ht.1.le⟩
      · intro x hx y hy hxy hdisjoint
        apply hregular x ⟨hx.1, hx.2.trans (ht.2.le.trans hT.2)⟩
          y ⟨hy.1, hy.2.trans (ht.2.le.trans hT.2)⟩ hxy
        apply disjoint_left.mpr
        intro z hz hzxy
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact (not_le_of_gt (hy.2.trans_lt ht.2)) hzxy.2
        · exact disjoint_left.mp hdisjoint hz hzxy
      · intro z hz
        exact hjump z (Finset.mem_insert_of_mem hz)
    have hlast : f b ≤ f T := by
      apply hregular T ⟨hT.1.le, hT.2⟩ b ⟨hab, le_rfl⟩ hT.2
      apply disjoint_left.mpr
      intro z hz hTz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (lt_irrefl _) hTz.1
      · exact (not_lt_of_gt (hST z hz)) hTz.1
    exact hlast.trans (hdrop.trans hL)
