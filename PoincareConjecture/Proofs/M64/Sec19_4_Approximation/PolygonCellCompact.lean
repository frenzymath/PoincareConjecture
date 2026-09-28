import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture




theorem m64PolygonCellSet_isClosed {N : ℕ} (j : Fin N) :
    IsClosed (m64PolygonCellSet j) := by
  change IsClosed {p : LoopPlane |
    m63CellLeft N j ≤ p 0 ∧ p 0 ≤ m63CellLeft N j + m63CellLength N ∧
      0 ≤ p 1 ∧ p 1 ≤ 1}
  let h0 : Continuous (fun p : LoopPlane => p 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  let h1 : Continuous (fun p : LoopPlane => p 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  exact (isClosed_le continuous_const h0).inter
    ((isClosed_le h0 continuous_const).inter
      ((isClosed_le continuous_const h1).inter
        (isClosed_le h1 continuous_const)))




theorem m64PolygonCellSet_subset_annulusDomain {N : ℕ} (hN : 0 < N)
    (j : Fin N) : m64PolygonCellSet j ⊆ m64AnnulusDomain := by
  intro p hp
  change 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
  change m63CellLeft N j ≤ p 0 ∧
    p 0 ≤ m63CellLeft N j + m63CellLength N ∧
      0 ≤ p 1 ∧ p 1 ≤ 1 at hp
  have hell : 0 < m63CellLength N := m63CellLength_pos hN
  have hleft : 0 ≤ m63CellLeft N j := by
    dsimp [m63CellLeft]
    exact mul_nonneg (Nat.cast_nonneg _) hell.le
  have hj : (j.val : ℝ) + 1 ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hright : m63CellLeft N j + m63CellLength N ≤ curvePeriod := by
    calc
      m63CellLeft N j + m63CellLength N =
          ((j.val : ℝ) + 1) * m63CellLength N := by
            dsimp [m63CellLeft]
            ring
      _ ≤ (N : ℝ) * m63CellLength N :=
        mul_le_mul_of_nonneg_right hj hell.le
      _ = curvePeriod := m63_count_mul_cellLength hN
  exact ⟨hleft.trans hp.1, hp.2.1.trans hright, hp.2.2.1, hp.2.2.2⟩




theorem m64PolygonCellSet_isCompact {N : ℕ} (hN : 0 < N) (j : Fin N) :
    IsCompact (m64PolygonCellSet j) := by
  exact m64AnnulusDomain_isCompact.of_isClosed_subset
    (m64PolygonCellSet_isClosed j)
    (m64PolygonCellSet_subset_annulusDomain hN j)

end PoincareConjecture
