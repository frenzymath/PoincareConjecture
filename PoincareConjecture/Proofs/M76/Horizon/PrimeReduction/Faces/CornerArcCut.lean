import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.NormalArcCuts
import PoincareConjecture.Proofs.M76.Mathlib.RectangleCornerArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc
import PoincareConjecture.Proofs.M76.Mathlib.TriangularRoof









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

def rimArc (a b : ℝ) : Set (ℝ × ℝ) := RectangleCornerArcs.cornerArc 0 a 0 b

def vertices : Set (ℝ × ℝ) := {(0, 0), (1, 0), (0, 1)}

theorem rimArc_ballPair {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsFinitePLBallPair ℝ (rimArc a b) {(0, b), (a, 0)} :=
  RectangleCornerArcs.cornerArc_ballPair ha.ne hb.ne

theorem rimArc_subset_frontier {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) : rimArc a b ⊆ frontier base := by
  rintro p (⟨hx, hy⟩ | ⟨hx, hy⟩)
  · have hx0 : p.1 = 0 := hx
    have hy0 : 0 ≤ p.2 := (uIcc_of_le hb.1.le ▸ hy).1
    have hy1 : p.2 ≤ 1 := ((uIcc_of_le hb.1.le ▸ hy).2).trans hb.2.le
    rw [frontier_base]
    change min p.1 (min p.2 (1 - p.1 - p.2)) = 0
    rw [hx0]
    exact min_eq_left (le_min hy0 (by linarith))
  · have hy0 : p.2 = 0 := hy
    have hx0 : 0 ≤ p.1 := (uIcc_of_le ha.1.le ▸ hx).1
    have hx1 : p.1 ≤ 1 := ((uIcc_of_le ha.1.le ▸ hx).2).trans ha.2.le
    rw [frontier_base]
    change min p.1 (min p.2 (1 - p.1 - p.2)) = 0
    rw [hy0, min_eq_left (show (0 : ℝ) ≤ 1 - p.1 - 0 by linarith), min_eq_right hx0]

theorem rimArc_inter_vertices {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) : rimArc a b ∩ vertices = {(0, 0)} := by
  ext p
  constructor
  · rintro ⟨hp, hpv⟩
    rcases hpv with rfl | rfl | rfl
    · rfl
    · simp only [rimArc, RectangleCornerArcs.cornerArc, uIcc_of_le ha.1.le,
        uIcc_of_le hb.1.le, mem_union, mem_prod, mem_singleton_iff,
        mem_Icc, zero_le_one, true_and, one_ne_zero, false_and, false_or, and_true] at hp
      exact False.elim ((not_le_of_gt ha.2) hp)
    · simp only [rimArc, RectangleCornerArcs.cornerArc, uIcc_of_le ha.1.le,
        uIcc_of_le hb.1.le, mem_union, mem_prod, mem_singleton_iff,
        mem_Icc, zero_le_one, true_and, one_ne_zero, and_false, or_false] at hp
      exact False.elim ((not_le_of_gt hb.2) hp)
  · rintro rfl
    exact ⟨Or.inl ⟨rfl, left_mem_uIcc⟩, Or.inl rfl⟩

theorem vertices_subset_frontier : vertices ⊆ frontier base := by
  rintro p (rfl | rfl | rfl) <;> norm_num [frontier_base, roof]




theorem exists_corner_arc_cut {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    {W : Set (ℝ × ℝ)} (hW : IsFinitePLBallPair ℝ W {(0, b), (a, 0)})
    (hproper : W \ {(0, b), (a, 0)} ⊆ base \ frontier base) :
    ∃ C D V : Set (ℝ × ℝ),
      IsFinitePLBallPair ℝ V {(0, b), (a, 0)} ∧
      rimArc a b ∪ V = frontier base ∧ rimArc a b ∩ V = {(0, b), (a, 0)} ∧
      IsFinitePLBallPair (ℝ × ℝ) C (rimArc a b ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) D (W ∪ V) ∧
      C ∪ D = base ∧ C ∩ D = W ∧
      C ∩ frontier base = rimArc a b ∧ D ∩ frontier base = V ∧
      C ∩ vertices = {(0, 0)} ∧ D ∩ vertices = {(1, 0), (0, 1)} := by
  have hne : ((0, b) : ℝ × ℝ) ≠ (a, 0) := fun h => ha.1.ne (congrArg Prod.fst h)
  have hU := rimArc_ballPair ha.1 hb.1
  obtain ⟨V, hV, hUV, hcommon⟩ := isFinitePLBallPair_base.exists_boundary_arc_complement
    hU (rimArc_subset_frontier ha hb) hne
  obtain ⟨C, D, hC, hD, hCD, hinter, hCB, hDB⟩ :=
    isFinitePLBallPair_base.exists_proper_arc_cut hU hV hW hne hcommon.subset hUV hproper
  have hCv : C ∩ vertices = {(0, 0)} := by
    calc
      C ∩ vertices = C ∩ (frontier base ∩ vertices) := by
        rw [inter_eq_right.mpr vertices_subset_frontier]
      _ = (C ∩ frontier base) ∩ vertices := (inter_assoc _ _ _).symm
      _ = {(0, 0)} := by rw [hCB, rimArc_inter_vertices ha hb]
  have hendv : Disjoint ({(0, b), (a, 0)} : Set (ℝ × ℝ)) vertices := by
    apply disjoint_left.mpr
    rintro p (rfl | rfl) (h | h | h)
    · exact hb.1.ne' (congrArg Prod.snd h)
    · exact zero_ne_one (congrArg Prod.fst h)
    · exact hb.2.ne (congrArg Prod.snd h)
    · exact ha.1.ne' (congrArg Prod.fst h)
    · exact ha.2.ne (congrArg Prod.fst h)
    · exact zero_ne_one (congrArg Prod.snd h)
  have hVv : V ∩ vertices = {(1, 0), (0, 1)} := by
    ext p
    constructor
    · rintro ⟨hpV, hpv⟩
      rcases hpv with rfl | rfl | rfl
      · have hpU : ((0, 0) : ℝ × ℝ) ∈ rimArc a b := Or.inl ⟨rfl, left_mem_uIcc⟩
        exact False.elim (disjoint_left.mp hendv (hcommon.subset ⟨hpU, hpV⟩) (Or.inl rfl))
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hp
      have hpv : p ∈ vertices := Or.inr hp
      refine ⟨?_, hpv⟩
      rcases hUV.symm.subset (vertices_subset_frontier hpv) with hpU | hpV
      · have hp0 := (rimArc_inter_vertices ha hb).subset ⟨hpU, hpv⟩
        rcases hp with rfl | rfl <;> norm_num at hp0
      · exact hpV
  refine ⟨C, D, V, hV, hUV, hcommon, hC, hD, hCD, hinter, hCB, hDB, hCv, ?_⟩
  calc
    D ∩ vertices = D ∩ (frontier base ∩ vertices) := by
      rw [inter_eq_right.mpr vertices_subset_frontier]
    _ = (D ∩ frontier base) ∩ vertices := (inter_assoc _ _ _).symm
    _ = {(1, 0), (0, 1)} := by rw [hDB, hVv]

end PoincareConjecture.M76.TriangleCorner
