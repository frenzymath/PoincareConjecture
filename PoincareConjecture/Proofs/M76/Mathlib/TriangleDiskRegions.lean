import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangleRegion
import PoincareConjecture.Proofs.M76.Mathlib.PolygonReindex

set_option autoImplicit false

open Set

namespace TriangleDiskModel

def rightTriangle : Polygon (ℝ × ℝ) 3 := ⟨![(0, 0), (1, 0), (0, 1)]⟩

def leftTriangle : Polygon (ℝ × ℝ) 3 := ⟨![(0, 1), (-1, 0), (0, 0)]⟩

def wholeTriangle : Polygon (ℝ × ℝ) 3 := ⟨![(-1, 0), (1, 0), (0, 1)]⟩

private theorem independent_horizontal {a b : ℝ} (hab : a ≠ b) :
    AffineIndependent ℝ ![(a, (0 : ℝ)), (b, 0), (0, 1)] := by
  let S : AffineSubspace ℝ (ℝ × ℝ) :=
    (affineSpan ℝ {(0 : ℝ)}).comap (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  have h : AffineIndependent ℝ ![(a, (0 : ℝ)), (0, 1), (b, 0)] := by
    apply affineIndependent_of_ne_of_mem_of_notMem_of_mem (s := S)
    · simpa only [ne_eq, Prod.mk.injEq, and_true] using hab
    · simp [S]
    · simp [S]
    · simp [S]
  exact h.comm_right

theorem independent_rightTriangle : AffineIndependent ℝ rightTriangle :=
  independent_horizontal (by norm_num)

theorem independent_leftTriangle : AffineIndependent ℝ leftTriangle :=
  (independent_horizontal (a := -1) (b := 0) (by norm_num)).comm_right.comm_left

theorem independent_wholeTriangle : AffineIndependent ℝ wholeTriangle :=
  independent_horizontal (by norm_num)

private theorem hull_le (P : Polygon (ℝ × ℝ) 3) (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (r : ℝ)
    (h : ∀ i, L (P i) ≤ r) {x : ℝ × ℝ} (hx : x ∈ convexHull ℝ (range P)) : L x ≤ r :=
  convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i) ((convex_Iic r).linear_preimage L) hx

private theorem hull_ge (P : Polygon (ℝ × ℝ) 3) (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (r : ℝ)
    (h : ∀ i, r ≤ L (P i)) {x : ℝ × ℝ} (hx : x ∈ convexHull ℝ (range P)) : r ≤ L x :=
  convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i) ((convex_Ici r).linear_preimage L) hx

theorem mem_right_region_iff (x : ℝ × ℝ) :
    x ∈ convexHull ℝ (range rightTriangle) ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1 := by
  constructor
  · intro hx
    exact ⟨hull_ge _ (LinearMap.fst ℝ ℝ ℝ) 0
      (by intro i; fin_cases i <;> norm_num [rightTriangle]) hx,
      hull_ge _ (LinearMap.snd ℝ ℝ ℝ) 0
        (by intro i; fin_cases i <;> norm_num [rightTriangle]) hx,
      hull_le _ (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ) 1
        (by intro i; fin_cases i <;> norm_num [rightTriangle]) hx⟩
  · rintro ⟨hx, hy, hsum⟩
    apply mem_convexHull_of_exists_fintype ![1 - x.1 - x.2, x.1, x.2] rightTriangle
    · intro i
      fin_cases i <;> dsimp <;> linarith
    · simp [Fin.sum_univ_succ]
    · exact mem_range_self
    · apply Prod.ext <;> simp [Fin.sum_univ_succ, rightTriangle]

theorem mem_left_region_iff (x : ℝ × ℝ) :
    x ∈ convexHull ℝ (range leftTriangle) ↔ x.1 ≤ 0 ∧ 0 ≤ x.2 ∧ x.2 - x.1 ≤ 1 := by
  constructor
  · intro hx
    exact ⟨hull_le _ (LinearMap.fst ℝ ℝ ℝ) 0
      (by intro i; fin_cases i <;> norm_num [leftTriangle]) hx,
      hull_ge _ (LinearMap.snd ℝ ℝ ℝ) 0
        (by intro i; fin_cases i <;> norm_num [leftTriangle]) hx,
      hull_le _ (LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ) 1
        (by intro i; fin_cases i <;> norm_num [leftTriangle]) hx⟩
  · rintro ⟨hx, hy, hsum⟩
    apply mem_convexHull_of_exists_fintype ![x.2, -x.1, 1 + x.1 - x.2] leftTriangle
    · intro i
      fin_cases i <;> dsimp <;> linarith
    · simp [Fin.sum_univ_succ]
      ring
    · exact mem_range_self
    · apply Prod.ext <;> simp [Fin.sum_univ_succ, leftTriangle]

theorem mem_whole_region_iff (x : ℝ × ℝ) :
    x ∈ convexHull ℝ (range wholeTriangle) ↔
      0 ≤ x.2 ∧ x.1 + x.2 ≤ 1 ∧ x.2 - x.1 ≤ 1 := by
  constructor
  · intro hx
    exact ⟨hull_ge _ (LinearMap.snd ℝ ℝ ℝ) 0
      (by intro i; fin_cases i <;> norm_num [wholeTriangle]) hx,
      hull_le _ (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ) 1
        (by intro i; fin_cases i <;> norm_num [wholeTriangle]) hx,
      hull_le _ (LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ) 1
        (by intro i; fin_cases i <;> norm_num [wholeTriangle]) hx⟩
  · rintro ⟨hy, hp, hm⟩
    apply mem_convexHull_of_exists_fintype
      ![(1 - x.2 - x.1) / 2, (1 - x.2 + x.1) / 2, x.2] wholeTriangle
    · intro i
      fin_cases i <;> dsimp <;> linarith
    · simp [Fin.sum_univ_succ]
      ring
    · exact mem_range_self
    · apply Prod.ext <;> simp [Fin.sum_univ_succ, wholeTriangle]
      ring

theorem mem_common_edge_iff (x : ℝ × ℝ) :
    x ∈ segment ℝ (0, 1) (0, 0) ↔ x.1 = 0 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    change a * 0 + b * 0 = 0 ∧ 0 ≤ a * 1 + b * 0 ∧ a * 1 + b * 0 ≤ 1
    exact ⟨by ring, by nlinarith, by nlinarith⟩
  · rintro ⟨hx, hy, hy'⟩
    refine ⟨x.2, 1 - x.2, hy, by linarith, by ring, ?_⟩
    apply Prod.ext <;> simp [hx]

theorem mem_open_common_edge_iff (x : ℝ × ℝ) :
    x ∈ openSegment ℝ (0, 1) (0, 0) ↔ x.1 = 0 ∧ 0 < x.2 ∧ x.2 < 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    change a * 0 + b * 0 = 0 ∧ 0 < a * 1 + b * 0 ∧ a * 1 + b * 0 < 1
    exact ⟨by ring, by nlinarith, by nlinarith⟩
  · rintro ⟨hx, hy, hy'⟩
    refine ⟨x.2, 1 - x.2, hy, by linarith, by ring, ?_⟩
    apply Prod.ext <;> simp [hx]

theorem region_union : convexHull ℝ (range rightTriangle) ∪ convexHull ℝ (range leftTriangle) =
    convexHull ℝ (range wholeTriangle) := by
  ext x
  simp only [mem_union, mem_right_region_iff, mem_left_region_iff, mem_whole_region_iff]
  constructor
  · rintro (⟨hx, hy, h⟩ | ⟨hx, hy, h⟩) <;> exact ⟨hy, by linarith, by linarith⟩
  · rintro ⟨hy, hp, hm⟩
    rcases le_total 0 x.1 with hx | hx
    · exact Or.inl ⟨hx, hy, hp⟩
    · exact Or.inr ⟨hx, hy, hm⟩

theorem region_inter : convexHull ℝ (range rightTriangle) ∩ convexHull ℝ (range leftTriangle) =
    segment ℝ (0, 1) (0, 0) := by
  ext x
  simp only [mem_inter_iff, mem_right_region_iff, mem_left_region_iff, mem_common_edge_iff]
  constructor
  · rintro ⟨⟨hx, hy, hp⟩, ⟨hx', _, hm⟩⟩
    exact ⟨by linarith, hy, by linarith⟩
  · rintro ⟨hx, hy, hy'⟩
    exact ⟨⟨by linarith, hy, by linarith⟩, ⟨by linarith, hy, by linarith⟩⟩

end TriangleDiskModel
