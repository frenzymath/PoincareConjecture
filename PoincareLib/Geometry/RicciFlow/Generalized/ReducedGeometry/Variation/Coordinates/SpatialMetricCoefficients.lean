import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.Realization
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Manifold.OpenSubsetChart
import PoincareLib.Geometry.Spacetime.Realization.OrdinaryProduct.Chart.Metric
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual spatial metric coefficients of the original L-action

Morgan-Tian Definition 6.2 and Lemma 6.4, pp. 106-108. M11's smooth
metric-chart coefficients equal the prescribed metric on an open
Euclidean spatial domain. The original-time kinetic coefficient has
the exact factor twice the square root of backward time.
-/

set_option autoImplicit false
-- Open-subset tangent fibers have the given Euclidean vector model.
set_option backward.isDefEq.respectTransparency false
-- The weighted metric takes values in a twice-nested Euclidean operator space.
set_option synthInstance.maxSize 2048

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M14

variable {n : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
  (g : ℝ → RiemannianMetric n U)

/-- M11's chart metric is the actual prescribed metric on an included
open-subset point, the metric identification in Definition 6.2, p. 106. -/
theorem ordinaryChartMetric_openSubset_apply (x y : U) (t : ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    Proofs.M11.ordinaryChartMetric g x (t, y.val) v w = (g t).inner y v w := by
  change (g t).inner ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y.val)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) x).symm y.val v)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) x).symm y.val w) = _
  rw [U.mfderiv_chartAt_symm_val]
  change (g t).inner ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y.val) v w = _
  rw [U.chartAt_symm_apply_val]

/-- The bilinear coefficient whose half-quadratic expression is the
original sqrt-weighted kinetic density, Definition 6.2, p. 106. -/
noncomputable def backwardMetricCoefficient (T : ℝ) (x : U)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (2 * Real.sqrt z.1) • Proofs.M11.ordinaryChartMetric g x (T - z.1, z.2)

/-- The weighted coefficient evaluates to the actual spatial metric
with the required factor two, Definition 6.2, p. 106. -/
theorem backwardMetricCoefficient_apply (T : ℝ) (x y : U) (t : ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    backwardMetricCoefficient U g T x (t, y.val) v w =
      (2 * Real.sqrt t) * (g (T - t)).inner y v w := by
  simp only [backwardMetricCoefficient, smul_apply, smul_eq_mul,
    ordinaryChartMetric_openSubset_apply]

/-- The weighted coefficient retains the metric's symmetry, the
quadratic action calculation of Lemma 6.4, pp. 107-108. -/
theorem backwardMetricCoefficient_symm (T : ℝ) (x : U)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) (v w : EuclideanSpace ℝ (Fin n)) :
    backwardMetricCoefficient U g T x z v w = backwardMetricCoefficient U g T x z w v := by
  change (2 * Real.sqrt z.1) * Proofs.M11.ordinaryChartMetric g x (T - z.1, z.2) v w =
    (2 * Real.sqrt z.1) * Proofs.M11.ordinaryChartMetric g x (T - z.1, z.2) w v
  rw [Proofs.M11.ordinaryChartMetric_symm g x (T - z.1) z.2 v w]

/-- The actual backward metric coefficients are smooth on every
positive parameter set whose clock remains in the supplied metric
domain, the coordinate regularity in Lemma 6.4, pp. 107-108. -/
theorem backwardMetricCoefficient_contDiffOn {K J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g K) (T : ℝ) (x : U)
    (hpos : ∀ t ∈ J, 0 < t) (htime : ∀ t ∈ J, T - t ∈ K) :
    ContDiffOn ℝ ∞ (backwardMetricCoefficient U g T x) (J ×ˢ (U : Set _)) := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  have hm := Proofs.M11.ordinaryChartMetric_smooth g K hg x
  have hmap : ContDiffOn ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (T - z.1, z.2))
      (J ×ˢ (U : Set _)) := (contDiffOn_const.sub contDiffOn_fst).prodMk contDiffOn_snd
  have hmem : MapsTo (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (T - z.1, z.2))
      (J ×ˢ (U : Set _)) (K ×ˢ (Proofs.M11.spatialChartDomain (n := n) x : Set _)) := by
    intro z hz
    refine ⟨htime z.1 hz.1, ?_⟩
    change z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).target
    rw [U.chartAt_target_eq]
    exact hz.2
  exact (contDiffOn_const.mul (contDiffOn_fst.sqrt (fun z hz => (hpos z.1 hz.1).ne'))).smul
    (hm.comp hmap hmem)

/-- Positive backward time preserves strict positivity of the actual
metric coefficient, the invertible-momentum input after Lemma 6.4,
pp. 107-108. -/
theorem backwardMetricCoefficient_pos (T : ℝ) (x : U) {t : ℝ} (ht : 0 < t)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < backwardMetricCoefficient U g T x (t, y) v v := by
  rw [show y = (⟨y, hy⟩ : U).val from rfl, backwardMetricCoefficient_apply]
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr ht)) ((g (T - t)).pos _ v hv)

end PoincareMT.M14
