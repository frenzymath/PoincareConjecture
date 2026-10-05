import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Curvature.ScalarControl
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Escape

/-!
# Scale control for overlapping necks

The center-in-carrier scale comparison used in Morgan--Tian Proposition
A.11, pp. 503-504, follows from normalized scalar control and the exact
center-scale normalization. At an arbitrary common point, normalized
scalar control in both necks gives scale and squared-scale ratio control.
Axial-angle, graph and middle-region conclusions remain separate
obligations. See the overlap-scale and arbitrary-overlap-scale derivations;
no O(epsilon^2) rate is asserted.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.EpsilonNeck

/-- The center-in-carrier scale comparison for Proposition A.11, pp. 503-504: an actual neck
centered anywhere inside a sufficiently small neck has almost the same
scale. The threshold is fixed before all neck and manifold data. -/
theorem exists_overlap_scale_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (N' : EpsilonNeck g), N'.center ∈ N.carrier → |N'.scale / N.scale - 1| < α := by
  have hp : ContinuousAt (fun x : ℝ => x ^ (-1 / 2 : ℝ)) 1 :=
    Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
  obtain ⟨delta, hdelta, hpower⟩ := Metric.continuousAt_iff.mp hp α hα
  obtain ⟨epsilon0, hpos, hcap, hscalar⟩ :=
    exists_normalized_scalar_control_on_carrier.{u} hdelta
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N hepsilon N' hcenter
  have h := hscalar N hepsilon N'.center hcenter
  rw [← N'.scalar_center_eq N.connection] at h
  have hclose := hpower (show dist
      (N.scale ^ 2 * N'.connection.scalarCurvature N'.center) 1 < delta by
    simpa only [Real.dist_eq] using h)
  have hscale : (N.scale ^ 2 : ℝ) ^ (-1 / 2 : ℝ) = N.scale⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul N.scale_pos.le]
    norm_num [Real.rpow_neg_one]
  rw [Real.mul_rpow (sq_nonneg N.scale) N'.scalar_center_pos.le,
    hscale, ← N'.scale_eq_scalar, Real.one_rpow] at hclose
  simpa only [Real.dist_eq, div_eq_mul_inv, mul_comm N'.scale] using hclose

/-- Proposition A.11(1), pp. 503-504: two sufficiently small necks with
any nonempty intersection have scale and squared-scale ratios close to
one. The two neck parameters need not be equal. -/
theorem exists_intersecting_scale_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      (N.carrier ∩ N'.carrier).Nonempty →
      |(N'.scale / N.scale) ^ 2 - 1| < α ∧ |N'.scale / N.scale - 1| < α := by
  let delta : ℝ := min (1 / 2) (α / 4)
  have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
  have hdhalf : delta ≤ 1 / 2 := min_le_left _ _
  have hdalpha : 4 * delta ≤ α := by linarith [min_le_right (1 / 2 : ℝ) (α / 4)]
  obtain ⟨epsilon0, hpos, hcap, hscalar⟩ :=
    exists_normalized_scalar_control_on_carrier.{u} hdelta
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hinter
  obtain ⟨x, hx, hx'⟩ := hinter
  have hR : N'.connection.scalarCurvature x = N.connection.scalarCurvature x := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    simp_rw [N'.connection.horizon_curvatureTensor_eq N.connection x]
  let a := N.scale ^ 2 * N.connection.scalarCurvature x
  let b := N'.scale ^ 2 * N.connection.scalarCurvature x
  let t := N'.scale / N.scale
  have ha : |a - 1| < delta := hscalar N hN x hx
  have hb : |b - 1| < delta := by
    simpa only [b, hR] using hscalar N' hN' x hx'
  have haHalf : 1 / 2 < a := by linarith [(abs_lt.mp ha).1]
  have haPos : 0 < a := by linarith
  have ht : 0 < t := div_pos N'.scale_pos N.scale_pos
  have hba : b - a = a * (t ^ 2 - 1) := by
    dsimp [a, b, t]
    field_simp [N.scale_pos.ne']
  have hab : |b - a| < 2 * delta := by
    have htriangle : |b - a| ≤ |b - 1| + |a - 1| := by
      simpa only [abs_sub_comm 1 a] using abs_sub_le b 1 a
    linarith
  rw [hba, abs_mul, abs_of_pos haPos] at hab
  have hsq : |t ^ 2 - 1| < 4 * delta := by
    nlinarith [abs_nonneg (t ^ 2 - 1)]
  have hfactor : |t ^ 2 - 1| = |t - 1| * (t + 1) := by
    rw [show t ^ 2 - 1 = (t - 1) * (t + 1) by ring, abs_mul,
      abs_of_pos (show 0 < t + 1 by linarith)]
  have hroot : |t - 1| ≤ |t ^ 2 - 1| := by
    rw [hfactor]
    nlinarith [abs_nonneg (t - 1)]
  exact ⟨hsq.trans_le hdalpha, hroot.trans_lt (hsq.trans_le hdalpha)⟩

/-- The positive center normalization in Definition 2.18, p. 31, gives
the inverse-squared scale as the center scalar curvature. -/
theorem scalar_center_eq_inv_scale_sq {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) :
    N.connection.scalarCurvature N.center = (N.scale ^ 2)⁻¹ := by
  rw [N.scale_eq_scalar, ← Real.rpow_natCast, ← Real.rpow_mul N.scalar_center_pos.le]
  norm_num [Real.rpow_neg_one]

/-- Both ratios displayed in Proposition A.11(1), pp. 503-504, are
uniformly close to one whenever the two small necks intersect. -/
theorem exists_intersecting_center_scalar_scale_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      (N.carrier ∩ N'.carrier).Nonempty →
      |N.connection.scalarCurvature N.center /
        N'.connection.scalarCurvature N'.center - 1| < α ∧
        |N.scale / N'.scale - 1| < α := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ := exists_intersecting_scale_control.{u} hα
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hinter
  have hratio : N.connection.scalarCurvature N.center /
      N'.connection.scalarCurvature N'.center = (N'.scale / N.scale) ^ 2 := by
    rw [N.scalar_center_eq_inv_scale_sq, N'.scalar_center_eq_inv_scale_sq, div_pow]
    field_simp [N.scale_pos.ne', N'.scale_pos.ne']
  rw [hratio]
  exact ⟨(hcontrol N N' hN hN' hinter).1,
    (hcontrol N' N hN' hN (by simpa only [Set.inter_comm] using hinter)).2⟩

end PoincareMT.EpsilonNeck
