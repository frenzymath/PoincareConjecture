import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.CornerArcCut
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

private theorem horizontal_order_implies_vertical_order
    {a b c d : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    {W Z : Set (ℝ × ℝ)} (hW : IsFinitePLBallPair ℝ W {(0, b), (a, 0)})
    (hZ : IsFinitePLBallPair ℝ Z {(0, d), (c, 0)})
    (hproperW : W \ {(0, b), (a, 0)} ⊆ base \ frontier base)
    (hproperZ : Z \ {(0, d), (c, 0)} ⊆ base \ frontier base)
    (hdis : Disjoint W Z) (hac : a < c) : b < d := by
  obtain ⟨C, D, V, _, _, _, hC, hD, hCD, hinter, hCB, _, _, _⟩ :=
    exists_corner_arc_cut hc hd hZ hproperZ
  have hWbase : W ⊆ base := by
    intro x hx
    by_cases hend : x ∈ ({(0, b), (a, 0)} : Set (ℝ × ℝ))
    · exact isFinitePLBallPair_base.1 ((rimArc_subset_frontier ha hb)
        ((rimArc_ballPair ha.1 hb.1).1 hend))
    · exact (hproperW ⟨hx, hend⟩).1
  have hxW : (a, (0 : ℝ)) ∈ W := hW.1 (by simp)
  have hxC : (a, (0 : ℝ)) ∈ C := hC.1 (Or.inl (Or.inr
    ⟨uIcc_of_le hc.1.le ▸ (show a ∈ Icc (0 : ℝ) c from ⟨ha.1.le, hac.le⟩), rfl⟩))
  have hWC : W ⊆ C := by
    rcases Dehn.isPreconnected_subset_one_cut_piece hW.isConnected.isPreconnected
        hC.isCompact.isClosed hD.isCompact.isClosed (hWbase.trans hCD.symm.subset)
        hinter hdis with hWC | hWD
    · exact hWC
    · exact False.elim (disjoint_left.mp hdis hxW (hinter.subset ⟨hxC, hWD hxW⟩))
  have hyW : ((0 : ℝ), b) ∈ W := hW.1 (by simp)
  have hyfront : ((0 : ℝ), b) ∈ frontier base :=
    rimArc_subset_frontier ha hb ((rimArc_ballPair ha.1 hb.1).1 (by simp))
  have hyU := hCB.subset ⟨hWC hyW, hyfront⟩
  have hbd : b ≤ d := by
    rcases hyU with hleft | hbottom
    · exact (uIcc_of_le hd.1.le ▸ hleft.2).2
    · exact False.elim (hb.1.ne' hbottom.2)
  have hne : b ≠ d := by
    intro he
    exact disjoint_left.mp hdis hyW (he.symm ▸ hZ.1 (by simp))
  exact lt_of_le_of_ne hbd hne



theorem endpoint_order_of_disjoint_arcs
    {a b c d : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    {W Z : Set (ℝ × ℝ)} (hW : IsFinitePLBallPair ℝ W {(0, b), (a, 0)})
    (hZ : IsFinitePLBallPair ℝ Z {(0, d), (c, 0)})
    (hproperW : W \ {(0, b), (a, 0)} ⊆ base \ frontier base)
    (hproperZ : Z \ {(0, d), (c, 0)} ⊆ base \ frontier base)
    (hdis : Disjoint W Z) : a ≠ c ∧ b ≠ d ∧ (a < c ↔ b < d) := by
  have hac : a ≠ c := by
    intro he
    exact disjoint_left.mp hdis (hW.1 (by simp)) (show (a, (0 : ℝ)) ∈ Z from
      he.symm ▸ hZ.1 (by simp))
  have hbd : b ≠ d := by
    intro he
    exact disjoint_left.mp hdis (hW.1 (by simp)) (show ((0 : ℝ), b) ∈ Z from
      he.symm ▸ hZ.1 (by simp))
  refine ⟨hac, hbd, ?_, ?_⟩
  · exact horizontal_order_implies_vertical_order ha hb hc hd hW hZ hproperW hproperZ hdis
  · intro hbd'
    rcases lt_or_gt_of_ne hac with hac | hca
    · exact hac
    · exact False.elim (lt_asymm hbd'
        (horizontal_order_implies_vertical_order hc hd ha hb hZ hW hproperZ hproperW
          hdis.symm hca))

end PoincareConjecture.M76.TriangleCorner
