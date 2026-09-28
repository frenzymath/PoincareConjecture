import PoincareConjecture.Definitions.M63Polygon
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ProfileBase

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}

theorem m64_polygon_map_eq_of_side_map_eq
    (P Q : M63GeodesicPolygon g D N) (hN : 0 < N)
    (hside : ∀ j : Fin N, ∀ s ∈ Icc (0 : ℝ) (m63CellLength N),
      (Q.side j).map s = (P.side j).map s) :
    ∀ x : ℝ, Q.map x = P.map x := by
  have hell : 0 < m63CellLength N := m63CellLength_pos hN
  have hNell : (N : ℝ) * m63CellLength N = curvePeriod :=
    m63_count_mul_cellLength hN
  have hcover {x : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      ∃ j : Fin N, ∃ s ∈ Icc (0 : ℝ) (m63CellLength N),
        x = m63CellLeft N j + s := by
    rcases lt_or_eq_of_le hx.2 with hlt | rfl
    · have hxdiv : 0 ≤ x / m63CellLength N := div_nonneg hx.1 hell.le
      have hj : Nat.floor (x / m63CellLength N) < N :=
        (Nat.floor_lt hxdiv).mpr
          ((div_lt_iff₀ hell).mpr (by simpa only [hNell] using hlt))
      let j : Fin N := ⟨Nat.floor (x / m63CellLength N), hj⟩
      refine ⟨j, x - m63CellLeft N j, ⟨?_, ?_⟩, by ring⟩
      · exact sub_nonneg.mpr ((le_div_iff₀ hell).mp (Nat.floor_le hxdiv))
      · have hh := (div_lt_iff₀ hell).mp
          (Nat.lt_floor_add_one (x / m63CellLength N))
        change x - (Nat.floor (x / m63CellLength N) : ℝ) *
          m63CellLength N ≤ m63CellLength N
        nlinarith only [hh]
    · let j : Fin N := ⟨N - 1, by omega⟩
      refine ⟨j, m63CellLength N, ⟨hell.le, le_rfl⟩, ?_⟩
      have hn : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        exact_mod_cast (by omega : N - 1 + 1 = N)
      change curvePeriod = ((N - 1 : ℕ) : ℝ) * m63CellLength N +
        m63CellLength N
      rw [← hNell, ← hn]
      ring
  intro x
  let k : ℤ := Int.floor (x / curvePeriod)
  let y : ℝ := x - (k : ℝ) * curvePeriod
  have hy : y ∈ Icc (0 : ℝ) curvePeriod := by
    have h0 := (le_div_iff₀ Real.two_pi_pos).mp
      (Int.floor_le (x / curvePeriod))
    have h1 := (div_lt_iff₀ Real.two_pi_pos).mp
      (Int.lt_floor_add_one (x / curvePeriod))
    dsimp only [y, k]
    dsimp only [curvePeriod] at h0 h1 ⊢
    constructor <;> linarith only [h0, h1]
  have hx : x = y + (k : ℝ) * curvePeriod := by
    dsimp only [y]
    ring
  rw [hx, Q.periodic.int_mul k y, P.periodic.int_mul k y]
  obtain ⟨j, s, hs, hy_eq⟩ := hcover hy
  rw [hy_eq]
  rw [Q.cell_agreement j s hs, P.cell_agreement j s hs]
  exact hside j s hs

end PoincareConjecture
