import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace Poincare

theorem properSpace_of_approximate_split {X : Type*} [MetricSpace X]
    [CompleteSpace X] [LocallyCompactSpace X]
    (hsplit : ∀ x y : X, ∀ r ε : ℝ, 0 < r → 0 < ε → r < dist x y →
      ∃ z, dist x z ≤ r ∧ dist z y < dist x y - r + ε) : ProperSpace X := by
  constructor
  intro x R
  let S : Set ℝ := {r | IsCompact (closedBall x r)}
  obtain ⟨r₀, hr₀, hc₀⟩ := exists_isCompact_closedBall x
  have hS : S.Nonempty := ⟨r₀, hc₀⟩
  have hunbounded : ¬ BddAbove S := by
    intro hb
    let a := sSup S
    have hr₀a : r₀ ≤ a := le_csSup hb hc₀
    have ha : 0 < a := hr₀.trans_le hr₀a
    have hca : IsCompact (closedBall x a) := by
      apply TotallyBounded.isCompact_of_isClosed _ isClosed_closedBall
      apply Metric.totallyBounded_iff.mpr
      intro ε hε
      have hmax : max (a - ε / 3) (r₀ / 2) < a := by
        apply max_lt <;> linarith
      obtain ⟨r, hcr, hr⟩ := (lt_csSup_iff hb hS).mp hmax
      have hrpos : 0 < r := by
        have := (le_max_right (a - ε / 3) (r₀ / 2)).trans_lt hr
        linarith
      have har : a - ε / 3 < r := (le_max_left _ _).trans_lt hr
      obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hcr.totallyBounded
        (ε / 3) (by linarith)
      refine ⟨t, ht, ?_⟩
      intro y hy
      have hxy : dist x y ≤ a := by simpa [dist_comm] using hy
      have hnear : ∃ z ∈ closedBall x r, dist y z < 2 * ε / 3 := by
        by_cases hyr : dist x y ≤ r
        · exact ⟨y, by simpa [dist_comm] using hyr, by simp; linarith⟩
        · obtain ⟨z, hxz, hzy⟩ := hsplit x y r (ε / 3) hrpos (by linarith)
            (lt_of_not_ge hyr)
          refine ⟨z, by simpa [dist_comm] using hxz, ?_⟩
          rw [dist_comm]
          linarith
      obtain ⟨z, hz, hyz⟩ := hnear
      obtain ⟨w, hwt, hzw⟩ := mem_iUnion₂.mp (hcover hz)
      refine mem_iUnion₂.mpr ⟨w, hwt, ?_⟩
      have hzw' : dist z w < ε / 3 := hzw
      have := dist_triangle y z w
      change dist y w < ε
      linarith
    obtain ⟨δ, hδ, hcδ⟩ := hca.exists_isCompact_cthickening
    have hlarge : IsCompact (closedBall x (a + δ / 2)) := by
      refine hcδ.of_isClosed_subset isClosed_closedBall ?_
      intro y hy
      have hxy : dist x y ≤ a + δ / 2 := by simpa [dist_comm] using hy
      by_cases hya : dist x y ≤ a
      · apply self_subset_cthickening (closedBall x a)
        simpa [dist_comm] using hya
      · obtain ⟨z, hxz, hzy⟩ := hsplit x y a (δ / 2) ha (by linarith)
          (lt_of_not_ge hya)
        apply mem_cthickening_of_dist_le y z δ (closedBall x a)
        · simpa [dist_comm] using hxz
        · rw [dist_comm]
          linarith
    have hle : a + δ / 2 ≤ a := le_csSup hb hlarge
    linarith
  obtain ⟨r, hcr, hRr⟩ := not_bddAbove_iff.mp hunbounded R
  exact hcr.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hRr.le)

end Poincare
