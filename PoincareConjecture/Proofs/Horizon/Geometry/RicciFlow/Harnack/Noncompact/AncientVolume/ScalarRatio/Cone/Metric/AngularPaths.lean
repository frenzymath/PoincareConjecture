import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Geodesics
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.QuadraticIdentity
import Mathlib.Topology.Path













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Topology NNReal Manifold ContDiff Bundle

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}


theorem dist_sq_asymptoticConeDilation (hc : RayComparison p) (a : ℝ≥0)
    (x z : AsymptoticCone p hc) :
    dist x (asymptoticConeDilation hc a z) ^ 2 =
      (a : ℝ) ^ 2 * (asymptoticConeRadius hc z : ℝ) ^ 2 +
        (asymptoticConeRadius hc x : ℝ) ^ 2 - a *
          ((asymptoticConeRadius hc z : ℝ) ^ 2 +
            (asymptoticConeRadius hc x : ℝ) ^ 2 - dist x z ^ 2) := by
  obtain ⟨⟨r, u⟩, rfl⟩ := surjective_asymptoticConeProjection hc x
  obtain ⟨⟨s, v⟩, rfl⟩ := surjective_asymptoticConeProjection hc z
  rw [asymptoticConeDilation_projection, dist_asymptoticConeProjection,
    dist_asymptoticConeProjection, asymptoticConeRadius_projection,
    asymptoticConeRadius_projection]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  push_cast
  ring


theorem asymptoticConeRadius_sq_interpolation (hc : RayComparison p)
    (x y z : AsymptoticCone p hc) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hxz : dist x z = t * dist x y) (hzy : dist z y = (1 - t) * dist x y) :
    (asymptoticConeRadius hc z : ℝ) ^ 2 =
      (1 - t) * (asymptoticConeRadius hc x : ℝ) ^ 2 +
        t * (asymptoticConeRadius hc y : ℝ) ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  obtain ⟨⟨r, u⟩, _⟩ := surjective_asymptoticConeProjection hc x
  let o := asymptoticConeProjection hc (0, u)
  have ho (w : AsymptoticCone p hc) : dist o w = asymptoticConeRadius hc w := by
    obtain ⟨⟨s, v⟩, rfl⟩ := surjective_asymptoticConeProjection hc w
    rw [dist_comm, dist_asymptoticConeProjection_zero, asymptoticConeRadius_projection]
  have hcone (a : ℝ) (ha : 0 < a) (v w : AsymptoticCone p hc) :
      dist v (asymptoticConeDilation hc a.toNNReal w) ^ 2 =
        a ^ 2 * dist o w ^ 2 + dist o v ^ 2 -
          a * (dist o w ^ 2 + dist o v ^ 2 - dist v w ^ 2) := by
    rw [dist_sq_asymptoticConeDilation, Real.coe_toNNReal _ ha.le, ho, ho]
  simpa only [ho] using radial_sq_interpolation_of_minimizing_segment o x y z
    (fun a => asymptoticConeDilation hc a.toNNReal) hcone ht hxz hzy


theorem asymptoticConeRadius_sq_on_metric_segment (hc : RayComparison p)
    (x y : AsymptoticCone p hc) (γ : ℝ → AsymptoticCone p hc)
    (hγ0 : γ 0 = x) (hγ1 : γ 1 = y)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (asymptoticConeRadius hc (γ t) : ℝ) ^ 2 =
      (1 - t) * (asymptoticConeRadius hc x : ℝ) ^ 2 +
        t * (asymptoticConeRadius hc y : ℝ) ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  apply asymptoticConeRadius_sq_interpolation hc x y (γ t) ht
  · simpa only [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1] using hγ 0 (by simp) t ht
  · simpa only [hγ1, abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using
      hγ t ht 1 (by simp)



theorem asymptoticConeRadius_lower_bound_on_unit_segment (hc : RayComparison p)
    (x y : AsymptoticConeUnitSlice p hc) (hxy : dist x y < 2)
    (γ : ℝ → AsymptoticCone p hc) (hγ0 : γ 0 = x.1) (hγ1 : γ 1 = y.1)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y) :
    0 < Real.sqrt (1 - dist x y ^ 2 / 4) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        (asymptoticConeRadius hc (γ t) : ℝ) ^ 2 =
          1 - t * (1 - t) * dist x y ^ 2 ∧
        Real.sqrt (1 - dist x y ^ 2 / 4) ≤ asymptoticConeRadius hc (γ t) := by
  have hpositive : 0 < 1 - dist x y ^ 2 / 4 := by
    nlinarith [dist_nonneg (x := x) (y := y)]
  refine ⟨Real.sqrt_pos.2 hpositive, ?_⟩
  intro t ht
  have heq := asymptoticConeRadius_sq_on_metric_segment hc x.1 y.1 γ hγ0 hγ1 hγ ht
  rw [x.property, y.property] at heq
  simp only [NNReal.coe_one, one_pow, mul_one] at heq
  have heq' : (asymptoticConeRadius hc (γ t) : ℝ) ^ 2 =
      1 - t * (1 - t) * dist x y ^ 2 := by
    change _ = 1 - t * (1 - t) * dist x.1 y.1 ^ 2
    linarith
  refine ⟨heq', ?_⟩
  apply (Real.sqrt_le_iff).2
  refine ⟨(asymptoticConeRadius hc (γ t)).coe_nonneg, ?_⟩
  rw [heq']
  nlinarith [mul_nonneg (sq_nonneg (t - 1 / 2)) (sq_nonneg (dist x y))]



theorem exists_normalized_path_of_metric_segment (hc : RayComparison p)
    (x y : AsymptoticConeUnitSlice p hc) (hxy : dist x y < 2)
    (γ : ℝ → AsymptoticCone p hc) (hγ0 : γ 0 = x.1) (hγ1 : γ 1 = y.1)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y) :
    ∃ P : Path x y, ∀ t : unitInterval,
      (P t).1 = asymptoticConeDilation hc (asymptoticConeRadius hc (γ t))⁻¹ (γ t) := by
  have hbound := asymptoticConeRadius_lower_bound_on_unit_segment hc x y hxy γ hγ0 hγ1 hγ
  have hpos (t : unitInterval) : 0 < asymptoticConeRadius hc (γ t) := by
    exact_mod_cast hbound.1.trans_le (hbound.2 t t.property).2
  have hcont : Continuous (fun t : unitInterval => γ t) := by
    apply (show LipschitzWith (Real.toNNReal (dist x y)) (fun t : unitInterval => γ t) from ?_).continuous
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [hγ s s.property t t.property, Real.coe_toNNReal _ dist_nonneg]
    change |(s : ℝ) - t| * dist x y ≤ dist x y * |(s : ℝ) - t|
    exact le_of_eq (mul_comm _ _)
  let c : unitInterval → AsymptoticConePositive p hc := fun t => ⟨γ t, hpos t⟩
  have hccont : Continuous c := hcont.subtype_mk hpos
  refine ⟨{
    toFun := fun t => asymptoticConeNormalize hc (c t)
    continuous_toFun := (continuous_asymptoticConeNormalize hc).comp hccont
    source' := ?_
    target' := ?_ }, fun _ => rfl⟩
  · apply Subtype.ext
    change asymptoticConeDilation hc (asymptoticConeRadius hc (γ 0))⁻¹ (γ 0) = x.1
    rw [hγ0, x.property, inv_one, asymptoticConeDilation_one]
  · apply Subtype.ext
    change asymptoticConeDilation hc (asymptoticConeRadius hc (γ 1))⁻¹ (γ 1) = y.1
    rw [hγ1, y.property, inv_one, asymptoticConeDilation_one]

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [NoncompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_asymptoticCone_angular_path
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∀ x y : AsymptoticConeUnitSlice p hc, dist x y < 2 →
      ∃ γ : ℝ → AsymptoticCone p hc, γ 0 = x.1 ∧ γ 1 = y.1 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y) ∧
        0 < Real.sqrt (1 - dist x y ^ 2 / 4) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          (asymptoticConeRadius hc (γ t) : ℝ) ^ 2 =
            1 - t * (1 - t) * dist x y ^ 2 ∧
          Real.sqrt (1 - dist x y ^ 2 / 4) ≤ asymptoticConeRadius hc (γ t)) ∧
        ∃ P : Path x y, ∀ t : unitInterval,
          (P t).1 = asymptoticConeDilation hc (asymptoticConeRadius hc (γ t))⁻¹ (γ t) := by
  let := g.toMetricSpace
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  dsimp only
  intro x y hxy
  obtain ⟨γ, hγ0, hγ1, hγ⟩ := g.exists_asymptoticCone_metric_segment D hcomplete hsec p x.1 y.1
  have hbound := asymptoticConeRadius_lower_bound_on_unit_segment hc x y hxy γ hγ0 hγ1 hγ
  exact ⟨γ, hγ0, hγ1, hγ, hbound.1, hbound.2,
    exists_normalized_path_of_metric_segment hc x y hxy γ hγ0 hγ1 hγ⟩

end PoincareConjecture.RiemannianMetric
