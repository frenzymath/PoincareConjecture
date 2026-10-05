import PoincareLib.Geometry.Riemannian.Surface.Boundary.Normalization
import PoincareLib.Geometry.Riemannian.Surface.Boundary.Corners
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Metric angles of tangent fans

Corner angles use the retained metric to normalize their two tangent rays.
Positive rescaling does not change them. Opposite rays give supplementary
angles, which constructs the angle sum of the four sectors at an arrangement
vertex without a choice of global orientation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

/-- The unoriented metric angle between two tangent rays. -/
noncomputable def cornerAngle (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) : ℝ :=
  Real.arccos (g.inner x
    ((Real.sqrt (g.inner x v v))⁻¹ • v)
    ((Real.sqrt (g.inner x w w))⁻¹ • w))

theorem cornerAngle_comm (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) :
    g.cornerAngle x v w = g.cornerAngle x w v := by
  unfold cornerAngle
  rw [g.symm]

theorem cornerAngle_smul_pos_left (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) {c : ℝ} (hc : 0 < c) :
    g.cornerAngle x (c • v) w = g.cornerAngle x v w := by
  unfold cornerAngle
  rw [g.normalize_smul_pos x v hc]

theorem cornerAngle_smul_pos_right (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) {c : ℝ} (hc : 0 < c) :
    g.cornerAngle x v (c • w) = g.cornerAngle x v w := by
  rw [g.cornerAngle_comm, g.cornerAngle_smul_pos_left x w v hc, g.cornerAngle_comm]

theorem cornerAngle_neg_left (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) :
    g.cornerAngle x (-v) w = Real.pi - g.cornerAngle x v w := by
  simp [cornerAngle, Real.arccos_neg]

theorem cornerAngle_neg_right (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) :
    g.cornerAngle x v (-w) = Real.pi - g.cornerAngle x v w := by
  rw [g.cornerAngle_comm, g.cornerAngle_neg_left, g.cornerAngle_comm x w v]

theorem cornerAngle_neg_neg (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) :
    g.cornerAngle x (-v) (-w) = g.cornerAngle x v w := by
  rw [g.cornerAngle_neg_left, g.cornerAngle_neg_right]
  ring

/-- Four coordinate sectors have total metric angle `2 * pi`, even when the
coordinate axes are not orthogonal for the metric. -/
theorem sum_cornerAngle_four_sectors (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) :
    (∑ i : Bool, ∑ j : Bool,
      g.cornerAngle x (if i then v else -v) (if j then w else -w)) =
      2 * Real.pi := by
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    g.cornerAngle_neg_left, g.cornerAngle_neg_right]
  ring

/-- Inserting a nonzero ray in a positive cone preserves the metric sector
angle. This is the local angle identity used when a cap is subdivided. -/
theorem cornerAngle_split_of_nonneg_combination (g : RiemannianMetric 2 S) (x : S)
    (v w : TangentSpace (𝓡 2) x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hne : a • v + b • w ≠ 0) :
    g.cornerAngle x v w = g.cornerAngle x v (a • v + b • w) +
      g.cornerAngle x (a • v + b • w) w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hang (u z : TangentSpace (𝓡 2) x) :
      g.cornerAngle x u z = InnerProductGeometry.angle u z := by
    unfold cornerAngle InnerProductGeometry.angle
    change Real.arccos (inner ℝ
      ((Real.sqrt (inner ℝ u u))⁻¹ • u) ((Real.sqrt (inner ℝ z z))⁻¹ • z)) = _
    simp only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _),
      real_inner_smul_left, inner_smul_right, mul_inv_rev, div_eq_mul_inv]
    congr 1
    ring
  simp only [hang]
  apply InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hne
  rw [Submodule.mem_span_pair]
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

end PoincareMT.RiemannianMetric
