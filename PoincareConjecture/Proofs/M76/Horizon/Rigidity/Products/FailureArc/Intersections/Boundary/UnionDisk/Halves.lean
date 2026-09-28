import PoincareConjecture.Proofs.M76.Mathlib.TriangleDiskPartition
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDiskModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc

set_option autoImplicit false
open Set TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryUnionDisk

local notation "P2" => (ℝ × ℝ)

def half (b : Bool) : Set P2 :=
  convexHull ℝ (range (if b then leftTriangle else rightTriangle))

def whole : Set P2 := convexHull ℝ (range wholeTriangle)

def seam : Set P2 := segment ℝ (0, 1) (0, 0)

theorem half_ball (b : Bool) : IsFinitePLBallPair P2 (half b) (frontier (half b)) := by
  cases b
  · exact rightTriangle.isFinitePLBallPair_convexHull_triangle independent_rightTriangle
  · exact leftTriangle.isFinitePLBallPair_convexHull_triangle independent_leftTriangle

theorem whole_ball : IsFinitePLBallPair P2 whole (frontier whole) :=
  wholeTriangle.isFinitePLBallPair_convexHull_triangle independent_wholeTriangle

theorem half_union : half false ∪ half true = whole := region_union

theorem half_inter : half false ∩ half true = seam := region_inter

theorem seam_ball : IsFinitePLBallPair ℝ seam {((0, 1) : P2), (0, 0)} := by
  have hab : ((0, 1) : P2) ≠ (0, 0) := by norm_num
  have h := isFinitePLBallPair_affine_interval zero_lt_one
    (ContinuousAffineMap.lineMap ((0, 1) : P2) (0, 0))
    (AffineMap.lineMap_injective ℝ hab).injOn
  simpa only [seam, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using h

theorem seam_subset_frontier (b : Bool) : seam ⊆ frontier (half b) := by
  intro x hx
  cases b
  · change x ∈ frontier (convexHull ℝ (range rightTriangle))
    rw [rightTriangle.frontier_convexHull_triangle independent_rightTriangle]
    simp only [Polygon.boundary, Polygon.edgeSet, rightTriangle,
      affineSegment_eq_segment]
    exact mem_iUnion.mpr ⟨2, hx⟩
  · change x ∈ frontier (convexHull ℝ (range leftTriangle))
    rw [leftTriangle.frontier_convexHull_triangle independent_leftTriangle]
    simp only [Polygon.boundary, Polygon.edgeSet, leftTriangle,
      affineSegment_eq_segment]
    refine mem_iUnion.mpr ⟨2, ?_⟩
    change x ∈ segment ℝ ((0, 0) : P2) (0, 1)
    exact (segment_symm ℝ ((0, 1) : P2) (0, 0)) ▸ hx

theorem exists_half_outer_intervals :
    ∃ U : Bool → Set P2, ∀ b,
      IsFinitePLBallPair ℝ (U b) {((0, 1) : P2), (0, 0)} ∧
      U b ∪ seam = frontier (half b) ∧ U b ∩ seam = {((0, 1) : P2), (0, 0)} ∧
      ∀ x ∈ half b, x ∈ frontier whole ↔ x ∈ U b := by
  have hab : ((0, 1) : P2) ≠ (0, 0) := by norm_num
  have hex (b : Bool) := (half_ball b).exists_boundary_arc_complement seam_ball
    (seam_subset_frontier b) hab
  choose U hU hcover hinter using hex
  refine ⟨U, fun b ↦ ⟨hU b, ?_, ?_, ?_⟩⟩
  · simpa only [union_comm] using hcover b
  · simpa only [inter_comm] using hinter b
  · intro x hx
    have hfront : x ∈ frontier whole ↔
        x ∈ frontier (half b) ∧ x ∉ openSegment ℝ ((0, 1) : P2) (0, 0) := by
      cases b
      · exact frontier_membership.1 x hx
      · exact frontier_membership.2 x hx
    have hseam : x ∈ seam ↔ x = (0, 1) ∨ x = (0, 0) ∨
        x ∈ openSegment ℝ ((0, 1) : P2) (0, 0) := by
      rw [seam, ← insert_endpoints_openSegment]
      simp only [mem_insert_iff]
    have hopen : x ∈ openSegment ℝ ((0, 1) : P2) (0, 0) →
        x ≠ (0, 1) ∧ x ≠ (0, 0) := by
      intro h
      have hh := (mem_open_common_edge_iff x).mp h
      constructor <;> intro heq <;> rw [heq] at hh <;> norm_num at hh
    rw [hfront, ← hcover b]
    have hi := Set.ext_iff.mp (hinter b) x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hi
    simp only [mem_union]
    constructor
    · rintro ⟨hS | hU', hn⟩
      · rcases hseam.mp hS with ha | hb | ho
        · exact (hi.mpr (Or.inl ha)).2
        · exact (hi.mpr (Or.inr hb)).2
        · exact (hn ho).elim
      · exact hU'
    · intro hu
      refine ⟨Or.inr hu, ?_⟩
      intro ho
      have he := hi.mp ⟨hseam.mpr (Or.inr (Or.inr ho)), hu⟩
      exact he.elim (hopen ho).1 (hopen ho).2

end PoincareConjecture.M76.Dehn.Annuli.BoundaryUnionDisk
