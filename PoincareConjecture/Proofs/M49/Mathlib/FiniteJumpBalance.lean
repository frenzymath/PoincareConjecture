import PoincareConjecture.Proofs.M49.Mathlib.FiniteJumps
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators

theorem add_sum_le_add_sum_of_finite_left_jumps {β : Type*}
    [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    [TopologicalSpace β] [OrderClosedTopology β] [ContinuousAdd β]
    {f loss gain : ℝ → β} {a b : ℝ} (S : Finset ℝ)
    (hab : a ≤ b) (hS : (S : Set ℝ) ⊆ Ioc a b)
    (hregular : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      Disjoint (S : Set ℝ) (Ioc x y) → f y ≤ f x)
    (hjump : ∀ T ∈ S, ∃ L, Tendsto f (𝓝[<] T) (𝓝 L) ∧
      f T + loss T ≤ L + gain T) :
    f b + ∑ T ∈ S, loss T ≤ f a + ∑ T ∈ S, gain T := by
  classical
  induction S using Finset.induction_on_max generalizing a b with
  | empty =>
    simpa only [Finset.sum_empty, add_zero] using
      hregular a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab (by simp)
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
    have hL : L + ∑ z ∈ S, loss z ≤ f a + ∑ z ∈ S, gain z := by
      apply le_of_tendsto (hlim.add_const (∑ z ∈ S, loss z))
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
    have hnot : T ∉ S := fun h => (lt_irrefl T) (hST T h)
    rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
    calc
      f b + (loss T + ∑ z ∈ S, loss z) =
          (f b + loss T) + ∑ z ∈ S, loss z := (add_assoc _ _ _).symm
      _ ≤ (L + gain T) + ∑ z ∈ S, loss z :=
        add_le_add ((add_le_add hlast le_rfl).trans hdrop) le_rfl
      _ = (L + ∑ z ∈ S, loss z) + gain T := by ac_rfl
      _ ≤ (f a + ∑ z ∈ S, gain z) + gain T := add_le_add hL le_rfl
      _ = f a + (gain T + ∑ z ∈ S, gain z) := by ac_rfl
