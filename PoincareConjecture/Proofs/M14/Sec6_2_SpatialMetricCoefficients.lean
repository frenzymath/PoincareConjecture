import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetChart
import PoincareConjecture.Proofs.M11.OrdinaryChartMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M14

variable {n : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
  (g : ℝ → RiemannianMetric n U)

theorem ordinaryChartMetric_openSubset_apply (x y : U) (t : ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    Proofs.M11.ordinaryChartMetric g x (t, y.val) v w = (g t).inner y v w := by
  change (g t).inner ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y.val)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) x).symm y.val v)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) x).symm y.val w) = _
  rw [U.mfderiv_chartAt_symm_val]
  change (g t).inner ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y.val) v w = _
  rw [U.chartAt_symm_apply_val]

noncomputable def backwardMetricCoefficient (T : ℝ) (x : U)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (2 * Real.sqrt z.1) • Proofs.M11.ordinaryChartMetric g x (T - z.1, z.2)

theorem backwardMetricCoefficient_apply (T : ℝ) (x y : U) (t : ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    backwardMetricCoefficient U g T x (t, y.val) v w =
      (2 * Real.sqrt t) * (g (T - t)).inner y v w := by
  simp only [backwardMetricCoefficient, smul_apply, smul_eq_mul,
    ordinaryChartMetric_openSubset_apply]

theorem backwardMetricCoefficient_symm (T : ℝ) (x : U)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) (v w : EuclideanSpace ℝ (Fin n)) :
    backwardMetricCoefficient U g T x z v w = backwardMetricCoefficient U g T x z w v := by
  change (2 * Real.sqrt z.1) * Proofs.M11.ordinaryChartMetric g x (T - z.1, z.2) v w =
    (2 * Real.sqrt z.1) * Proofs.M11.ordinaryChartMetric g x (T - z.1, z.2) w v
  rw [Proofs.M11.ordinaryChartMetric_symm g x (T - z.1) z.2 v w]

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

theorem backwardMetricCoefficient_pos (T : ℝ) (x : U) {t : ℝ} (ht : 0 < t)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < backwardMetricCoefficient U g T x (t, y) v v := by
  rw [show y = (⟨y, hy⟩ : U).val from rfl, backwardMetricCoefficient_apply]
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr ht)) ((g (T - t)).pos _ v hv)

end PoincareConjecture.M14
