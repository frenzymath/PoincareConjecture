import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonCellCompact
import Mathlib.Analysis.Convex.Measure












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture




theorem m64PolygonCellSet_convex {N : ℕ} (j : Fin N) :
    Convex ℝ (m64PolygonCellSet j) := by
  intro x hx y hy a b ha hb hab
  change m63CellLeft N j ≤ (a • x + b • y) 0 ∧
    (a • x + b • y) 0 ≤ m63CellLeft N j + m63CellLength N ∧
      0 ≤ (a • x + b • y) 1 ∧ (a • x + b • y) 1 ≤ 1
  change m63CellLeft N j ≤ x 0 ∧ x 0 ≤ m63CellLeft N j + m63CellLength N ∧
    0 ≤ x 1 ∧ x 1 ≤ 1 at hx
  change m63CellLeft N j ≤ y 0 ∧ y 0 ≤ m63CellLeft N j + m63CellLength N ∧
    0 ≤ y 1 ∧ y 1 ≤ 1 at hy
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      m63CellLeft N j = a * m63CellLeft N j + b * m63CellLeft N j := by
        rw [← add_mul, hab, one_mul]
      _ ≤ a * x 0 + b * y 0 := add_le_add
        (mul_le_mul_of_nonneg_left hx.1 ha)
        (mul_le_mul_of_nonneg_left hy.1 hb)
  · calc
      a * x 0 + b * y 0 ≤
          a * (m63CellLeft N j + m63CellLength N) +
            b * (m63CellLeft N j + m63CellLength N) :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
          (mul_le_mul_of_nonneg_left hy.2.1 hb)
      _ = m63CellLeft N j + m63CellLength N := by rw [← add_mul, hab, one_mul]
  · exact add_nonneg (mul_nonneg ha hx.2.2.1) (mul_nonneg hb hy.2.2.1)
  · calc
      a * x 1 + b * y 1 ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2.2.2 ha)
          (mul_le_mul_of_nonneg_left hy.2.2.2 hb)
      _ = 1 := by rw [← add_mul, hab, one_mul]




theorem m64_polygon_cells_cover {N : ℕ} (hN : 0 < N) :
    ∀ p ∈ m64AnnulusDomain, ∃ j : Fin N, p ∈ m64PolygonCellSet j := by
  intro p hp
  have hell : 0 < m63CellLength N := m63CellLength_pos hN
  have hNell : (N : ℝ) * m63CellLength N = curvePeriod :=
    m63_count_mul_cellLength hN
  have hleft : 0 ≤ p 0 := hp.1
  rcases lt_or_eq_of_le hp.2.1 with hlt | hperiod
  · have hdiv : 0 ≤ p 0 / m63CellLength N := div_nonneg hleft hell.le
    have hj : Nat.floor (p 0 / m63CellLength N) < N :=
      (Nat.floor_lt hdiv).mpr ((div_lt_iff₀ hell).mpr (by simpa [hNell] using hlt))
    let j : Fin N := ⟨Nat.floor (p 0 / m63CellLength N), hj⟩
    refine ⟨j, ?_⟩
    change m63CellLeft N j ≤ p 0 ∧
      p 0 ≤ m63CellLeft N j + m63CellLength N ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
    have hfloor : (Nat.floor (p 0 / m63CellLength N) : ℝ) ≤
        p 0 / m63CellLength N := Nat.floor_le hdiv
    have hnext := Nat.lt_floor_add_one (p 0 / m63CellLength N)
    refine ⟨?_, ?_, hp.2.2.1, hp.2.2.2⟩
    · exact (le_div_iff₀ hell).mp hfloor
    · dsimp [m63CellLeft]
      have hnext' : p 0 / m63CellLength N <
          (Nat.floor (p 0 / m63CellLength N) : ℝ) + 1 := hnext
      apply (div_lt_iff₀ hell).mp at hnext'
      linarith
  · let j : Fin N := ⟨N - 1, by omega⟩
    refine ⟨j, ?_⟩
    change m63CellLeft N j ≤ p 0 ∧
      p 0 ≤ m63CellLeft N j + m63CellLength N ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
    have hn : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      exact_mod_cast (by omega : N - 1 + 1 = N)
    refine ⟨?_, ?_, hp.2.2.1, hp.2.2.2⟩
    · have hle : m63CellLeft N j ≤ curvePeriod := by
        dsimp [j, m63CellLeft]
        rw [← hNell]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Nat.sub_le N 1)) hell.le
      exact hle.trans_eq hperiod.symm
    · dsimp [j, m63CellLeft]
      calc
        p 0 = curvePeriod := hperiod
        _ = ((N - 1 : ℕ) : ℝ) * m63CellLength N + m63CellLength N := by
          rw [← hNell, ← hn]
          ring
        _ ≤ ((N - 1 : ℕ) : ℝ) * m63CellLength N + m63CellLength N := le_rfl





theorem m64_polygon_cells_interior_ae {N : ℕ} (hN : 0 < N) :
    ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      ∃ j : Fin N, p ∈ interior (m64PolygonCellSet j) := by
  have hfront : ∀ j : Fin N,
      volume (frontier (m64PolygonCellSet j)) = 0 := by
    intro j
    exact Convex.addHaar_frontier volume (m64PolygonCellSet_convex j)
  have hfront_union : volume (⋃ j : Fin N, frontier (m64PolygonCellSet j)) = 0 :=
    measure_iUnion_null hfront
  let U : Set LoopPlane := ⋃ j : Fin N, interior (m64PolygonCellSet j)
  have hbad : volume (m64AnnulusDomain \ U) = 0 := by
    apply measure_mono_null _ hfront_union
    intro p hp
    obtain ⟨j, hj⟩ := m64_polygon_cells_cover hN p hp.1
    have hnot : p ∉ interior (m64PolygonCellSet j) := by
      intro hi
      exact hp.2 (show p ∈ U from mem_iUnion.mpr ⟨j, hi⟩)
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change p ∈ closure (m64PolygonCellSet j) \ interior (m64PolygonCellSet j)
    exact ⟨subset_closure hj, hnot⟩
  apply (ae_restrict_iff' m64AnnulusDomain_measurableSet).2
  apply ae_iff.mpr
  have hcomp : {p : LoopPlane |
      ¬ (p ∈ m64AnnulusDomain → ∃ j : Fin N,
        p ∈ interior (m64PolygonCellSet j))} =
      m64AnnulusDomain \ U := by
    ext p
    simp [U]
  rw [hcomp]
  exact hbad

end PoincareConjecture
