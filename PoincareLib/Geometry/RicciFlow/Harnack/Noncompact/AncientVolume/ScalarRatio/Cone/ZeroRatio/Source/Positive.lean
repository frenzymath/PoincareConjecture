import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.UnitNeighborhood

/-!
# Positive-radius realizations of the annular overlap quotient

The uniform metric bounds and prescribed unit centers keep every compact
coordinate-ball realization away from the cone vertex. The actual overlap
quotient realization therefore lifts to the canonical positive cone, retaining
openness, its exact range, unit-slice coverage, and chart distance identities.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Gluing Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {X : Type*} [MetricSpace X] {p : X}

/-- A compact metric coordinate ball centered on a unit direction stays in
the quantitative radial interval prescribed by the global tangent bounds. -/
theorem coneRadius_bounds_of_isometric_coordinateBall
    (hc : RayComparison p) (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r)
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ g.tangentNorm x v ∧ g.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : basedMinimizingRays p) (e : MetricCoordinateBall g r → AsymptoticCone p hc)
    (he : Isometry e)
    (hcenter : e ⟨0, Metric.mem_closedBall_self hr.le⟩ = asymptoticConeRayProjection hc (1, η))
    (x : MetricCoordinateBall g r) :
    1 - 3 * r / 2 ≤ (asymptoticConeRadius hc (e x) : ℝ) ∧
      (asymptoticConeRadius hc (e x) : ℝ) ≤ 1 + 3 * r / 2 := by
  let o : MetricCoordinateBall g r := ⟨0, Metric.mem_closedBall_self hr.le⟩
  have hx : ‖x.val‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  have hdist : dist (e x) (e o) ≤ 3 * r / 2 := by
    rw [he.dist_eq, dist_comm, MetricCoordinateBall.dist_eq]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (g.edist_bounds_of_uniform_tangentNorm_bounds hbound 0 x.val).2
    simp only [sub_zero, ENNReal.toReal_ofReal (by positivity : 0 ≤ 3 * ‖x.val‖ / 2)] at h
    exact h.trans (by linarith)
  have hrad : asymptoticConeRadius hc (e o) = 1 := by
    rw [show e o = asymptoticConeRayProjection hc (1, η) from hcenter]
    rfl
  have habs := (lipschitzWith_asymptoticConeRadius hc).dist_le_mul (e x) (e o)
  rw [hrad, NNReal.dist_eq] at habs
  simp only [NNReal.coe_one, one_mul] at habs
  have hh := abs_le.mp (habs.trans hdist)
  constructor <;> linarith [hh.1, hh.2]

theorem coneRadius_pos_of_isometric_coordinateBall
    (hc : RayComparison p) (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8)
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ g.tangentNorm x v ∧ g.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : basedMinimizingRays p) (e : MetricCoordinateBall g r → AsymptoticCone p hc)
    (he : Isometry e)
    (hcenter : e ⟨0, Metric.mem_closedBall_self hr.le⟩ = asymptoticConeRayProjection hc (1, η))
    (x : MetricCoordinateBall g r) : 0 < asymptoticConeRadius hc (e x) := by
  have h := (coneRadius_bounds_of_isometric_coordinateBall hc g hr hbound η e he hcenter x).1
  change (0 : ℝ) < (asymptoticConeRadius hc (e x) : ℝ)
  linarith

theorem coneRadius_pos_uniformBallRestriction
    (hc : RayComparison p) (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8)
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ g.tangentNorm x v ∧ g.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : basedMinimizingRays p) (e : MetricCoordinateBall g r → AsymptoticCone p hc)
    (he : Isometry e)
    (hcenter : e ⟨0, Metric.mem_closedBall_self hr.le⟩ = asymptoticConeRayProjection hc (1, η))
    (x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) :
    0 < asymptoticConeRadius hc (g.uniformBallRestriction hr e x) :=
  coneRadius_pos_of_isometric_coordinateBall hc g hr hrsmall hbound η e he hcenter _

/-- Joint surjectivity of the actual quotient inclusions propagates the
coordinate radius bounds to every point of its realization. -/
theorem coneRadius_pos_of_quotient_coordinateRealization
    (hc : RayComparison p) (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8)
    (hbound : ∀ j (x v : EuclideanSpace ℝ (Fin n)),
      ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧ (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : ℕ → basedMinimizingRays p)
    (e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc)
    (he : ∀ j, Isometry (e j))
    (hcenter : ∀ j, e j ⟨0, Metric.mem_closedBall_self hr.le⟩ =
      asymptoticConeRayProjection hc (1, η j))
    (O : OverlapSystem (fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)))
    (f : Quotient O.setoid → AsymptoticCone p hc)
    (hinclude : ∀ j x, f (O.include j x) = (g j).uniformBallRestriction hr (e j) x) :
    ∀ q, 0 < asymptoticConeRadius hc (f q) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
    rcases a with ⟨j, x⟩
    change 0 < asymptoticConeRadius hc (f (O.include j x))
    rw [hinclude]
    exact coneRadius_pos_uniformBallRestriction hc (g j) hr hrsmall (hbound j)
      (η j) (e j) (he j) (hcenter j) x

end PoincareMT.RiemannianMetric

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p)
  {Q : Type*} (f : Q → AsymptoticCone p hc)
  (hpos : ∀ q, 0 < asymptoticConeRadius hc (f q))

/-- The canonical positive-radius lift of an actual cone realization. -/
def positiveConeRealization : Q → AsymptoticConePositive p hc :=
  fun q => ⟨f q, hpos q⟩

@[simp] theorem positiveConeRealization_val (q : Q) :
    (positiveConeRealization hc f hpos q).val = f q := rfl

theorem range_positiveConeRealization :
    range (positiveConeRealization hc f hpos) = Subtype.val ⁻¹' range f := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, Subtype.ext hq⟩

theorem isOpenEmbedding_positiveConeRealization [TopologicalSpace Q]
    (hf : Topology.IsOpenEmbedding f) :
    Topology.IsOpenEmbedding (positiveConeRealization hc f hpos) := by
  refine ⟨(Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp hf.isEmbedding, ?_⟩
  rw [range_positiveConeRealization]
  exact hf.isOpen_range.preimage continuous_subtype_val

theorem unitSlice_subset_range_positiveConeRealization
    (hunit : {z : AsymptoticCone p hc | asymptoticConeRadius hc z = 1} ⊆ range f) :
    {z : AsymptoticConePositive p hc | asymptoticConeRadius hc z.val = 1} ⊆
      range (positiveConeRealization hc f hpos) := by
  rw [range_positiveConeRealization]
  exact fun _ hz => hunit hz

@[simp] theorem positiveConeRealization_preimage_unitSlice :
    positiveConeRealization hc f hpos ⁻¹'
      {z : AsymptoticConePositive p hc | asymptoticConeRadius hc z.val = 1} =
      f ⁻¹' {z : AsymptoticCone p hc | asymptoticConeRadius hc z = 1} := rfl

/-- Any already-established intrinsic distance identity on the positive cone
computes distances of this lift by the original full-cone realization. -/
theorem positiveConeRealization_metric_edist
    {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) (AsymptoticConePositive p hc)]
    [IsManifold (𝓡 n) ∞ (AsymptoticConePositive p hc)]
    (gP : PoincareMT.RiemannianMetric n (AsymptoticConePositive p hc))
    (hmetric : ∀ x y, gP.edist x y = EDist.edist x y) (x y : Q) :
    gP.edist (positiveConeRealization hc f hpos x) (positiveConeRealization hc f hpos y) =
      EDist.edist (f x) (f y) := by
  rw [hmetric]
  rfl

end Poincare.AncientVolume.ScalarRatio

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {X : Type*} [MetricSpace X] {p : X}

/-- An actual small coordinate realization lifts openly to the canonical
positive cone. The lift retains its full range and unit-slice coverage. -/
theorem exists_positive_quotient_realization
    (hc : RayComparison p) (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8)
    (hbound : ∀ j (x v : EuclideanSpace ℝ (Fin n)),
      ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧ (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : ℕ → basedMinimizingRays p)
    (e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc)
    (he : ∀ j, Isometry (e j))
    (hcenter : ∀ j, e j ⟨0, Metric.mem_closedBall_self hr.le⟩ =
      asymptoticConeRayProjection hc (1, η j))
    (O : OverlapSystem (fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)))
    (f : Quotient O.setoid → AsymptoticCone p hc) (hf : Topology.IsOpenEmbedding f)
    (hinclude : ∀ j x, f (O.include j x) = (g j).uniformBallRestriction hr (e j) x)
    (hunit : {z : AsymptoticCone p hc | asymptoticConeRadius hc z = 1} ⊆ range f) :
    ∃ fP : Quotient O.setoid → AsymptoticConePositive p hc,
      Topology.IsOpenEmbedding fP ∧ (∀ q, (fP q).val = f q) ∧
      (∀ j x, (fP (O.include j x)).val = (g j).uniformBallRestriction hr (e j) x) ∧
      range fP = Subtype.val ⁻¹' range f ∧
      {z : AsymptoticConePositive p hc | asymptoticConeRadius hc z.val = 1} ⊆ range fP ∧
      fP ⁻¹' {z : AsymptoticConePositive p hc | asymptoticConeRadius hc z.val = 1} =
        f ⁻¹' {z : AsymptoticCone p hc | asymptoticConeRadius hc z = 1} := by
  have hpos := coneRadius_pos_of_quotient_coordinateRealization hc g hr hrsmall hbound
    η e he hcenter O f hinclude
  exact ⟨positiveConeRealization hc f hpos,
    isOpenEmbedding_positiveConeRealization hc f hpos hf, fun _ => rfl, hinclude,
    range_positiveConeRealization hc f hpos,
    unitSlice_subset_range_positiveConeRealization hc f hpos hunit, rfl⟩

/-- The positive lift preserves every chart's actual limit distances for
the canonical subtype metric, without any intrinsic target-distance input. -/
theorem positive_quotient_realization_chart_dist
    (hc : RayComparison p) (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r)
    (e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc)
    (he : ∀ j, Isometry (e j))
    (O : OverlapSystem (fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)))
    (fP : Quotient O.setoid → AsymptoticConePositive p hc)
    (hinclude : ∀ j x, (fP (O.include j x)).val = (g j).uniformBallRestriction hr (e j) x)
    (j : ℕ) (x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) :
    dist (fP (O.include j x)) (fP (O.include j y)) = ((g j).edist x.val y.val).toReal := by
  change dist (fP (O.include j x)).val (fP (O.include j y)).val = _
  rw [hinclude, hinclude]
  exact (g j).uniformBallRestriction_dist hr (e j) (he j) x y

/-- The ambient distance identity also gives the chartwise intrinsic
distance identity for the constructed positive-cone metric. -/
theorem positive_quotient_realization_chart_edist
    (hc : RayComparison p) (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r)
    (e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc)
    (he : ∀ j, Isometry (e j))
    (O : OverlapSystem (fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)))
    (fP : Quotient O.setoid → AsymptoticConePositive p hc)
    (hinclude : ∀ j x, (fP (O.include j x)).val = (g j).uniformBallRestriction hr (e j) x)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (AsymptoticConePositive p hc)]
    [IsManifold (𝓡 n) ∞ (AsymptoticConePositive p hc)]
    (gP : RiemannianMetric n (AsymptoticConePositive p hc))
    (hmetric : ∀ x y, gP.edist x y = EDist.edist x y)
    (j : ℕ) (x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) :
    gP.edist (fP (O.include j x)) (fP (O.include j y)) = (g j).edist x.val y.val := by
  rw [hmetric]
  change EDist.edist (fP (O.include j x)).val (fP (O.include j y)).val = _
  rw [hinclude, hinclude]
  exact (g j).uniformBallRestriction_edist hr (e j) (he j) x y

end PoincareMT.RiemannianMetric
