import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SampledPolygonLength

set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}

theorem m64PolygonLength_eq_sampled_chord_sum
    (polygon : M63GeodesicPolygon g D N) (hN : 0 < N)
    (gamma : ℝ → M)
    (_hperiodic : Function.Periodic gamma curvePeriod)
    (_hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hvertices : ∀ j : Fin N,
      polygon.vertices j = gamma (m63CellLeft N j)) :
    m64PolygonLength polygon =
      ∑ j : Fin N,
        (g.edist (gamma (m63CellLeft N j))
          (gamma (m63CellLeft N (finRotate N j)))).toReal := by
  rw [m64PolygonLength_eq_sum polygon hN]
  apply Finset.sum_congr rfl
  intro j hj
  let ell : ℝ := m63CellLength N
  have hell : 0 ≤ ell := (m63CellLength_pos hN).le
  have hspeed : 0 ≤ (polygon.side j).speed :=
    (polygon.side j).speed_nonnegative
  have hdist := (polygon.side j).edist_eq_length hell
  have hdist' : g.edist (gamma (m63CellLeft N j))
      (gamma (m63CellLeft N (finRotate N j))) =
      ENNReal.ofReal (m63CellLength N * (polygon.side j).speed) := by
    calc
      g.edist (gamma (m63CellLeft N j))
          (gamma (m63CellLeft N (finRotate N j))) =
          g.edist (polygon.vertices j) (polygon.vertices (finRotate N j)) := by
            rw [hvertices j, hvertices (finRotate N j)]
      _ = ENNReal.ofReal (m63CellLength N * (polygon.side j).speed) := hdist
  have hnon : 0 ≤ ell * (polygon.side j).speed :=
    mul_nonneg hell hspeed
  symm
  rw [hdist', ENNReal.toReal_ofReal hnon]

end PoincareConjecture
