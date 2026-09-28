import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.VolumeComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Model
import Mathlib.Analysis.Normed.Module.Normalize

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped Topology NNReal ENNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {n : ℕ}

private theorem dist_smul_sphere
    (r s : ℝ≥0)
    (u v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    dist ((r : ℝ) • (u : EuclideanSpace ℝ (Fin n)))
      ((s : ℝ) • (v : EuclideanSpace ℝ (Fin n))) =
      Real.sqrt (((r : ℝ) - s) ^ 2 + r * s * dist u v ^ 2) := by
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hv : ‖(v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  have hsquare : dist ((r : ℝ) • (u : EuclideanSpace ℝ (Fin n)))
      ((s : ℝ) • (v : EuclideanSpace ℝ (Fin n))) ^ 2 =
      ((r : ℝ) - s) ^ 2 + r * s * dist u v ^ 2 := by
    simp only [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg,
      abs_of_nonneg s.coe_nonneg, real_inner_smul_left, real_inner_smul_right, hu, hv]
    ring
  rw [← hsquare, Real.sqrt_sq dist_nonneg]

def asymptoticConeEuclideanMap (hcomparison : RayComparison p)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    AsymptoticCone p hcomparison → EuclideanSpace ℝ (Fin n) := by
  exact @SeparationQuotient.lift (ℝ≥0 × AsymptoticLink p hcomparison)
    (EuclideanSpace ℝ (Fin n))
    (conePairPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace
    (fun a => (a.1 : ℝ) • (e a.2 : EuclideanSpace ℝ (Fin n))) (fun a b hab => by
      apply dist_eq_zero.mp
      rw [dist_smul_sphere, e.dist_eq]
      exact @Inseparable.dist_eq_zero _ (conePairPseudoMetric hcomparison) a b hab)

@[simp] theorem asymptoticConeEuclideanMap_projection (hcomparison : RayComparison p)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (a : ℝ≥0 × AsymptoticLink p hcomparison) :
    asymptoticConeEuclideanMap hcomparison e (asymptoticConeProjection hcomparison a) =
      (a.1 : ℝ) • (e a.2 : EuclideanSpace ℝ (Fin n)) := rfl

theorem isometry_asymptoticConeEuclideanMap (hcomparison : RayComparison p)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Isometry (asymptoticConeEuclideanMap hcomparison e) := by
  apply Isometry.of_dist_eq
  intro a b
  obtain ⟨a, rfl⟩ := surjective_asymptoticConeProjection hcomparison a
  obtain ⟨b, rfl⟩ := surjective_asymptoticConeProjection hcomparison b
  rw [asymptoticConeEuclideanMap_projection, asymptoticConeEuclideanMap_projection,
    dist_smul_sphere, e.dist_eq, dist_asymptoticConeProjection]

theorem norm_asymptoticConeEuclideanMap (hcomparison : RayComparison p)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (z : AsymptoticCone p hcomparison) :
    ‖asymptoticConeEuclideanMap hcomparison e z‖ = asymptoticConeRadius hcomparison z := by
  obtain ⟨a, rfl⟩ := surjective_asymptoticConeProjection hcomparison z
  have hu : ‖(e a.2 : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using (e a.2).property
  simp only [asymptoticConeEuclideanMap_projection, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg a.1.coe_nonneg, hu, mul_one, asymptoticConeRadius_projection]

theorem surjective_asymptoticConeEuclideanMap (hcomparison : RayComparison p)
    (hn : 1 ≤ n)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Function.Surjective (asymptoticConeEuclideanMap hcomparison e) := by
  let : NeZero n := ⟨by omega⟩
  intro x
  by_cases hx : x = 0
  · obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin n))).mpr
      (show (0 : ℝ) ≤ 1 by norm_num)
    refine ⟨asymptoticConeProjection hcomparison (0, e.symm ⟨u, hu⟩), ?_⟩
    simp [hx]
  · let u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      ⟨NormedSpace.normalize x, by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hx⟩
    refine ⟨asymptoticConeProjection hcomparison (‖x‖₊, e.symm u), ?_⟩
    rw [asymptoticConeEuclideanMap_projection, e.apply_symm_apply]
    exact NormedSpace.norm_smul_normalize x

def asymptoticConeEuclideanIsometry (hcomparison : RayComparison p) (hn : 1 ≤ n)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    AsymptoticCone p hcomparison ≃ᵢ EuclideanSpace ℝ (Fin n) where
  toEquiv := Equiv.ofBijective (asymptoticConeEuclideanMap hcomparison e)
    ⟨(isometry_asymptoticConeEuclideanMap hcomparison e).injective,
      surjective_asymptoticConeEuclideanMap hcomparison hn e⟩
  isometry_toFun := isometry_asymptoticConeEuclideanMap hcomparison e

@[simp] theorem asymptoticConeEuclideanIsometry_apply (hcomparison : RayComparison p)
    (hn : 1 ≤ n)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (z : AsymptoticCone p hcomparison) :
    asymptoticConeEuclideanIsometry hcomparison hn e z =
      asymptoticConeEuclideanMap hcomparison e z := rfl

theorem image_asymptoticCone_radial_ball (hcomparison : RayComparison p) (hn : 1 ≤ n)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (R : ℝ) :
    asymptoticConeEuclideanIsometry hcomparison hn e ''
      {z | (asymptoticConeRadius hcomparison z : ℝ) < R} =
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right, asymptoticConeEuclideanIsometry_apply,
      norm_asymptoticConeEuclideanMap] using hz
  · intro hx
    obtain ⟨z, rfl⟩ := (asymptoticConeEuclideanIsometry hcomparison hn e).surjective x
    refine ⟨z, ?_, rfl⟩
    simpa only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right, asymptoticConeEuclideanIsometry_apply,
      norm_asymptoticConeEuclideanMap] using hx

theorem asymptoticCone_radial_unit_ball_volume_of_chordal_isometry
    (hcomparison : RayComparison p) (hn : 1 ≤ n)
    (e : AsymptoticLink p hcomparison ≃ᵢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measure.euclideanHausdorffMeasure n
      {z : AsymptoticCone p hcomparison | asymptoticConeRadius hcomparison z < 1} =
        ENNReal.ofReal (PoincareConjecture.RiemannianMetric.euclideanUnitBallVolume n) := by
  let E := asymptoticConeEuclideanIsometry hcomparison hn e
  have hmeasure (s : Set (AsymptoticCone p hcomparison)) :
      Measure.euclideanHausdorffMeasure n (E '' s) = Measure.euclideanHausdorffMeasure n s := by
    simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
      E.hausdorffMeasure_image]
  have hball : E '' {z | asymptoticConeRadius hcomparison z < 1} =
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    convert image_asymptoticCone_radial_ball hcomparison hn e 1 using 2
    ext z
    exact_mod_cast (Iff.rfl : asymptoticConeRadius hcomparison z < 1 ↔
      asymptoticConeRadius hcomparison z < 1)
  rw [← hmeasure, hball, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    PoincareConjecture.RiemannianMetric.euclideanUnitBallVolume,
    ENNReal.ofReal_toReal measure_ball_lt_top.ne]

end Poincare.AncientVolume.ScalarRatio
