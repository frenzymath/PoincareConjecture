import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set

namespace Geometry

theorem exists_open_vertical_triangle_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E} (hu : u ≠ 0) {a b : ℝ} (ha : a < 0) (hb : 0 < b) (c : ℝ) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (0 : E × ℝ) ∈ U ∧
      ∀ x ∈ U,
        x ∈ convexHull ℝ ({(0, a), (0, b), (u, c)} : Set (E × ℝ)) ↔
          ∃ t : ℝ, 0 ≤ t ∧ x.1 = t • u := by
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one ℝ hu
  let psi := phi.toContinuousLinearMap
  let A : E × ℝ → ℝ := fun x =>
    (b * (1 - psi x.1) - x.2 + c * psi x.1) / (b - a)
  let B : E × ℝ → ℝ := fun x =>
    (x.2 - a * (1 - psi x.1) - c * psi x.1) / (b - a)
  have hcontA : Continuous A := by dsimp only [A]; fun_prop
  have hcontB : Continuous B := by dsimp only [B]; fun_prop
  have hab : 0 < b - a := sub_pos.mpr (ha.trans hb)
  let U := {x : E × ℝ | 0 < A x} ∩ {x : E × ℝ | 0 < B x}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const hcontA).inter (isOpen_lt continuous_const hcontB)
  have hzero : (0 : E × ℝ) ∈ U := by
    constructor
    · simpa [A] using div_pos hb hab
    · simpa [B] using div_pos (neg_pos.mpr ha) hab
  let C : Set (E × ℝ) := {x | ∃ t : ℝ, 0 ≤ t ∧ x.1 = t • u}
  have hcv : Convex ℝ C := by
    intro x hx y hy r s hr hs _
    obtain ⟨tx, htx, hx⟩ := hx
    obtain ⟨ty, hty, hy⟩ := hy
    refine ⟨r * tx + s * ty, add_nonneg (mul_nonneg hr htx) (mul_nonneg hs hty), ?_⟩
    change r • x.1 + s • y.1 = (r * tx + s * ty) • u
    rw [hx, hy, add_smul, mul_smul, mul_smul]
  have hverts : ({(0, a), (0, b), (u, c)} : Set (E × ℝ)) ⊆ C := by
    rintro x (rfl | rfl | rfl)
    · exact ⟨0, le_rfl, (zero_smul ℝ u).symm⟩
    · exact ⟨0, le_rfl, (zero_smul ℝ u).symm⟩
    · exact ⟨1, zero_le_one, (one_smul ℝ u).symm⟩
  refine ⟨U, hU, hzero, ?_⟩
  intro x hx
  constructor
  · exact fun h => convexHull_min hverts hcv h
  · rintro ⟨t, ht, hxt⟩
    have hpsi : psi x.1 = t := by
      rw [hxt, map_smul]
      change t * phi u = t
      rw [hphi, mul_one]
    have hsum : A x + B x + t = 1 := by
      dsimp only [A, B]
      rw [hpsi]
      field_simp [hab.ne']
      ring
    have hvalue : A x * a + B x * b + t * c = x.2 := by
      dsimp only [A, B]
      rw [hpsi]
      field_simp [hab.ne']
      ring
    apply mem_convexHull_of_exists_fintype ![A x, B x, t] ![(0, a), (0, b), (u, c)]
    · intro i
      fin_cases i
      · exact hx.1.le
      · exact hx.2.le
      · exact ht
    · simpa [Fin.sum_univ_succ, add_assoc] using hsum
    · intro i
      fin_cases i <;> simp
    · apply Prod.ext
      · simpa [Fin.sum_univ_succ] using hxt.symm
      · simpa [Fin.sum_univ_succ, add_assoc] using hvalue

end Geometry
