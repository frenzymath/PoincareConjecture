import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.UniformConeDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity.MeasureComparison

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}

instance asymptoticCone_measurableSpace (hcomparison : RayComparison p) :
    MeasurableSpace (AsymptoticCone p hcomparison) := borel _

instance asymptoticCone_borelSpace (hcomparison : RayComparison p) :
    BorelSpace (AsymptoticCone p hcomparison) := ⟨rfl⟩

def rescaledRayRange (p : X) (L : ℝ) : Set X :=
  Set.range (fun a : ℝ≥0 × basedMinimizingRays p => rayExtension a.2 (a.1 * L))

theorem exists_lipschitzOn_source_ray_projection
    (hcomparison : RayComparison p) [Nonempty (basedMinimizingRays p)]
    {L : ℝ} (hL : 0 < L) :
    ∃ π : X → AsymptoticCone p hcomparison,
      (∀ a : ℝ≥0 × basedMinimizingRays p,
        π (rayExtension a.2 (a.1 * L)) = asymptoticConeRayProjection hcomparison a) ∧
      LipschitzOnWith (L.toNNReal⁻¹) π (rescaledRayRange p L) := by
  classical
  let e := fun a : ℝ≥0 × basedMinimizingRays p => rayExtension a.2 (a.1 * L)
  let v := asymptoticConeRayProjection hcomparison
    (0, Classical.choice (inferInstance : Nonempty (basedMinimizingRays p)))
  let π := fun x : X => if hx : x ∈ Set.range e then
    asymptoticConeRayProjection hcomparison (Classical.choose hx) else v
  have hπ (a : ℝ≥0 × basedMinimizingRays p) :
      π (e a) = asymptoticConeRayProjection hcomparison a := by
    have ha : e a ∈ Set.range e := ⟨a, rfl⟩
    simp only [π, dif_pos ha]
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    have h := cone_distance_le_rescaled_ray_distance hcomparison
      (Classical.choose ha).2 a.2 (Classical.choose ha).1 a.1 hL
    change dist _ _ ≤ dist (e (Classical.choose ha)) (e a) / L at h
    simpa only [Classical.choose_spec ha, dist_self, zero_div] using h
  refine ⟨π, hπ, LipschitzOnWith.of_dist_le_mul ?_⟩
  rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
  rw [hπ, hπ, NNReal.coe_inv, Real.coe_toNNReal _ hL.le]
  simpa only [inv_mul_eq_div] using
    cone_distance_le_rescaled_ray_distance hcomparison a.2 b.2 a.1 b.1 hL

theorem image_source_ray_ball_eq_cone_radial_ball
    (hcomparison : RayComparison p) {L : ℝ} (hL : 0 < L)
    (π : X → AsymptoticCone p hcomparison)
    (hπ : ∀ a : ℝ≥0 × basedMinimizingRays p,
      π (rayExtension a.2 (a.1 * L)) = asymptoticConeRayProjection hcomparison a) :
    π '' (rescaledRayRange p L ∩ Metric.ball p L) =
      {z : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison z < 1} := by
  have hdist (r : ℝ≥0) (γ : basedMinimizingRays p) :
      dist (rayExtension γ (r * L)) p = r * L := by
    have h := rayExtension_dist γ (mul_nonneg r.coe_nonneg hL.le) le_rfl
    simpa only [rayExtension_zero, sub_zero, abs_of_nonneg
      (mul_nonneg r.coe_nonneg hL.le)] using h
  ext z
  constructor
  · rintro ⟨x, ⟨⟨a, rfl⟩, hx⟩, rfl⟩
    rw [hπ]
    change a.1 < 1
    have hx' : (a.1 : ℝ) * L < L := by simpa only [Metric.mem_ball, hdist] using hx
    exact_mod_cast (mul_lt_iff_lt_one_left hL).mp hx'
  · intro hz
    obtain ⟨a, rfl⟩ := surjective_asymptoticConeProjection hcomparison z
    obtain ⟨γ, hγ⟩ := surjective_asymptoticLinkProjection hcomparison a.2
    refine ⟨rayExtension γ (a.1 * L), ⟨⟨(a.1, γ), rfl⟩, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, hdist]
      change a.1 < 1 at hz
      have hz' : (a.1 : ℝ) < 1 := by exact_mod_cast hz
      nlinarith
    · rw [hπ (a.1, γ)]
      simp only [asymptoticConeRayProjection, hγ, Prod.mk.eta]

theorem cone_radial_ball_volume_le_source_ball
    [MeasurableSpace X] [BorelSpace X]
    (hcomparison : RayComparison p) [Nonempty (basedMinimizingRays p)]
    (n : ℕ) {L : ℝ} (hL : 0 < L) :
    Measure.euclideanHausdorffMeasure n
      {z : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison z < 1} ≤
      (ENNReal.ofReal L)⁻¹ ^ n * Measure.euclideanHausdorffMeasure n (Metric.ball p L) := by
  obtain ⟨π, hπ, hLip⟩ := exists_lipschitzOn_source_ray_projection hcomparison hL
  rw [← image_source_ray_ball_eq_cone_radial_ball hcomparison hL π hπ]
  calc
    _ ≤ ((L.toNNReal⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n *
        Measure.euclideanHausdorffMeasure n (rescaledRayRange p L ∩ Metric.ball p L) :=
      Poincare.HausdorffDensity.euclideanHausdorffMeasure_image_le
        (hLip.mono inter_subset_left) n
    _ ≤ (ENNReal.ofReal L)⁻¹ ^ n * Measure.euclideanHausdorffMeasure n (Metric.ball p L) := by
      rw [ENNReal.coe_inv (by positivity : L.toNNReal ≠ 0), ENNReal.ofReal]
      gcongr
      exact inter_subset_right

end Poincare.AncientVolume.ScalarRatio
