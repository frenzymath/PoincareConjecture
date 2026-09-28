import PoincareConjecture.Proofs.M76.Mathlib.TriangularPointedRim
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

theorem isFinitePLBallPair_upper_rim :
    IsFinitePLBallPair ℝ (frontier base ∩ {p | 1 ≤ cornerHeight p})
      (frontier base ∩ {p | cornerHeight p = 1}) := by
  obtain ⟨p, hp, hph⟩ := cornerHeight_interior_section_nonempty
    (show (1 / 2 : ℝ) ∈ Ioo 0 2 from by constructor <;> norm_num)
  obtain ⟨q, hq, hqh⟩ := cornerHeight_interior_section_nonempty
    (show (1 : ℝ) ∈ Ioo 0 2 from by constructor <;> norm_num)
  let A := cornerHeight.toAffineMap - AffineMap.const ℝ (ℝ × ℝ) 1
  have hneg : ∃ p ∈ interior base, A p < 0 := by
    refine ⟨p, hp, ?_⟩
    change cornerHeight p - 1 < 0
    change cornerHeight p = 1 / 2 at hph
    linarith
  have hplane : ∃ q ∈ interior base, A q = 0 :=
    ⟨q, hq, sub_eq_zero.mpr hqh⟩
  have hcopy := isFinitePLBallPair_base
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hcopy
  have hcv : Convex ℝ base := by rw [base_eq_triangle]; exact convex_convexHull ℝ _
  have h := K.isFinitePLBallPair_convex_frontier_affine_cap (F := ℝ) hK isCompact_base
    hcv hspace A hneg hplane (by simp)
  have hcap : {p : ℝ × ℝ | 0 ≤ A p} = {p | 1 ≤ cornerHeight p} := by
    ext p
    change 0 ≤ cornerHeight p - 1 ↔ 1 ≤ cornerHeight p
    exact sub_nonneg
  have hrim : {p : ℝ × ℝ | A p = 0} = {p | cornerHeight p = 1} := by
    ext p
    exact sub_eq_zero
  rwa [hcap, hrim] at h

end TriangularRoofModel

namespace Set

open TriangularRoofModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_twoInterval_circle_model {a b q : Set E}
    (ha : IsFinitePLBallPair ℝ a q) (hb : IsFinitePLBallPair ℝ b q)
    (hinter : a ∩ b = q) :
    ∃ H : (a ∪ b : Set E) ≃ₜ frontier base, H.IsFinitePL := by
  let U := frontier base ∩ {p | 1 ≤ cornerHeight p}
  let D := frontier base ∩ {p | cornerHeight p ≤ 1}
  let Q := frontier base ∩ {p | cornerHeight p = 1}
  have hU : IsFinitePLBallPair ℝ U Q := isFinitePLBallPair_upper_rim
  have hD : IsFinitePLBallPair ℝ D Q := isFinitePLBallPair_cornerHeight_rim_sublevel
    (show (1 : ℝ) ∈ Ioo 0 2 from by constructor <;> norm_num)
  have hUD : U ∩ D = Q := by
    ext p
    change ((p ∈ frontier base ∧ 1 ≤ cornerHeight p) ∧
      p ∈ frontier base ∧ cornerHeight p ≤ 1) ↔ p ∈ frontier base ∧ cornerHeight p = 1
    exact ⟨fun h => ⟨h.1.1, le_antisymm h.2.2 h.1.2⟩,
      fun h => ⟨⟨h.1, h.2.ge⟩, ⟨h.1, h.2.le⟩⟩⟩
  have hcover : U ∪ D = frontier base := by
    ext p
    change (p ∈ frontier base ∧ 1 ≤ cornerHeight p) ∨
      (p ∈ frontier base ∧ cornerHeight p ≤ 1) ↔ p ∈ frontier base
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hp
      rcases le_total 1 (cornerHeight p) with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
  obtain ⟨e, he, heq⟩ := hb.exists_homeomorph hD
  obtain ⟨H, hH, _⟩ := ha.exists_union_homeomorph_of_boundary_piece hU hinter hUD e he heq
  exact ⟨(Homeomorph.setCongr (rfl : a ∪ b = a ∪ b)).trans
    (H.trans (Homeomorph.setCongr hcover)), hH.setCongr rfl hcover⟩

end Set
