import PoincareConjecture.Proofs.M76.Mathlib.ConvexCubeNormalization

set_option autoImplicit false

open Set Geometry
open scoped BigOperators

namespace Geometry

variable {ι : Type*} [Fintype ι]

theorem sum_lt_card_of_mem_cube_ne_one {x : ι → ℝ}
    (hx : x ∈ Metric.closedBall (0 : ι → ℝ) 1) (hne : x ≠ fun _ => 1) :
    ∑ i, x i < (Fintype.card ι : ℝ) := by
  have hn : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hle (i : ι) : x i ≤ 1 :=
    (signedCubeCoordinate_le_norm (.inl i) x).trans hn
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hlt : x i < 1 := lt_of_le_of_ne (hle i) hi
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hle j)
      ⟨i, Finset.mem_univ i, hlt⟩

theorem exists_cube_cutting_level [Nonempty ι] {s : Set (ι → ℝ)}
    (hs : IsCompact s) (hsub : s ⊆ Metric.closedBall (0 : ι → ℝ) 1)
    (hp : (fun _ : ι => (1 : ℝ)) ∉ s) :
    ∃ r : ℝ, -(Fintype.card ι : ℝ) < r ∧ r < Fintype.card ι ∧
      ∀ x ∈ s, ∑ i, x i < r := by
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hne : s.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hs.exists_isMaxOn hne
      (by fun_prop : Continuous (fun y : ι → ℝ => ∑ i, y i)).continuousOn
    have hxlt := sum_lt_card_of_mem_cube_ne_one (hsub hx) (fun he => hp (he ▸ hx))
    have hlt : max (∑ i, x i) (-(Fintype.card ι : ℝ)) < Fintype.card ι :=
      max_lt hxlt (by linarith)
    obtain ⟨r, hr, hrn⟩ := exists_between hlt
    exact ⟨r, (le_max_right _ _).trans_lt hr, hrn,
      fun y hy => (hmax hy).trans_lt ((le_max_left _ _).trans_lt hr)⟩
  · refine ⟨0, by linarith, hcard, fun x hx => ?_⟩
    exact (hne ⟨x, hx⟩).elim

end Geometry
