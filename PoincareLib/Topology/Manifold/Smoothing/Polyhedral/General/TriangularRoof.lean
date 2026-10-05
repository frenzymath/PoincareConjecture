import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineMinimum
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineHalfspaceGeometry
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.TriangleDiskRegions
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolygonFinitePLDiskModel

/-!
# A finite PL roof over the standard triangle

The minimum of the three triangle coordinates is nonnegative on
the closed triangle, positive in its interior and zero exactly on
its frontier. Its finite affine formulas provide the cap disks
used in Alexander's attachment, p. 7. See M76 derivation 128.
-/

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

/-- The three affine coordinates of the standard planar triangle.
See M76 derivation 128. -/
def coordinates : Fin 3 → (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  ![(LinearMap.fst ℝ ℝ ℝ).toAffineMap, (LinearMap.snd ℝ ℝ ℝ).toAffineMap,
    AffineMap.const ℝ (ℝ × ℝ) 1 - (LinearMap.fst ℝ ℝ ℝ).toAffineMap -
      (LinearMap.snd ℝ ℝ ℝ).toAffineMap]

/-- The closed triangle serving as the common attachment disk.
See M76 derivation 128. -/
def base : Set (ℝ × ℝ) := {p | ∀ i, 0 ≤ coordinates i p}

/-- The height of the three-piece affine cap over the triangle.
See M76 derivation 128. -/
def roof (p : ℝ × ℝ) : ℝ := min p.1 (min p.2 (1 - p.1 - p.2))

/-- The coordinate inequalities define the actual standard
triangle convex hull. See M76 derivation 128. -/
theorem base_eq_triangle :
    base = convexHull ℝ (range TriangleDiskModel.rightTriangle) := by
  ext p
  rw [TriangleDiskModel.mem_right_region_iff]
  simp only [base, mem_ofPred_eq, coordinates, Fin.forall_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
  change (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 0 ≤ 1 - p.1 - p.2) ↔
    (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1)
  constructor <;> rintro ⟨hx, hy, hz⟩ <;> exact ⟨hx, hy, by linarith⟩

/-- The triangular attachment base is compact.
See M76 derivation 128. -/
theorem isCompact_base : IsCompact base := by
  rw [base_eq_triangle]
  exact (finite_range _).isCompact_convexHull ℝ

/-- The attachment base is a finite PL disk with its entire
frontier. See M76 derivation 128. -/
theorem isFinitePLBallPair_base : IsFinitePLBallPair (ℝ × ℝ) base (frontier base) := by
  rw [base_eq_triangle]
  exact TriangleDiskModel.rightTriangle.isFinitePLBallPair_convexHull_triangle
    TriangleDiskModel.independent_rightTriangle

/-- Nonnegative roof height is equivalent to base membership.
See M76 derivation 128. -/
theorem roof_nonneg_iff (p : ℝ × ℝ) : 0 ≤ roof p ↔ p ∈ base := by
  simp [roof, base, coordinates, Fin.forall_fin_succ]

/-- The interior of the base is exactly the positive-roof region.
See M76 derivation 128. -/
theorem interior_base : interior base = {p | 0 < roof p} := by
  have hnonzero (i : Fin 3) : (-(coordinates i)).linear ≠ 0 := by
    intro h
    have hv := LinearMap.congr_fun h ((1, 1) : ℝ × ℝ)
    fin_cases i <;> norm_num [coordinates] at hv
  have hbase : base = {p | ∀ i, (-(coordinates i)) p ≤ 0} := by
    ext p
    simp [base]
  rw [hbase, interior_finite_affine_halfspaces _ hnonzero]
  ext p
  simp [roof, coordinates, Fin.forall_fin_succ]

/-- The whole base frontier is exactly the zero-roof set.
See M76 derivation 128. -/
theorem frontier_base : frontier base = {p | roof p = 0} := by
  rw [frontier, isCompact_base.isClosed.closure_eq, interior_base]
  ext p
  change (p ∈ base ∧ ¬ 0 < roof p) ↔ roof p = 0
  constructor
  · rintro ⟨hp, hn⟩
    exact le_antisymm (not_lt.mp hn) ((roof_nonneg_iff p).mpr hp)
  · intro hp
    exact ⟨(roof_nonneg_iff p).mp hp.ge, by simp [hp]⟩

/-- The roof lies below each of the three affine coordinates.
See M76 derivation 128. -/
theorem roof_le_coordinate (p : ℝ × ℝ) (i : Fin 3) : roof p ≤ coordinates i p := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- The roof has an actual finite piecewise-affine certificate
on its whole triangular base. See M76 derivation 128. -/
theorem finitePiecewiseAffineOn_roof : FinitePiecewiseAffineOn roof base := by
  have hbase := isFinitePLBallPair_base
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hbase
  rw [← hspace]
  apply K.finitePiecewiseAffineOn_of_affine_minimum hK coordinates
  intro p _
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image (fun i => coordinates i p)
    Finset.univ_nonempty
  refine ⟨i, le_antisymm (roof_le_coordinate p i) ?_, roof_le_coordinate p⟩
  exact le_min (hi 0 (Finset.mem_univ _))
    (le_min (hi 1 (Finset.mem_univ _)) (hi 2 (Finset.mem_univ _)))

end TriangularRoofModel
