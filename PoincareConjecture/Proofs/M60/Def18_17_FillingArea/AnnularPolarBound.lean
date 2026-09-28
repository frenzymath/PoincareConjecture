import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration

set_option autoImplicit false

open Set MeasureTheory Metric Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m60AreaIntegral_annulus_le_polar
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (f : LoopPlane → M)
    {K : ℝ} (hK : 0 ≤ K) (ell : ℝ → ℝ) (hell : Continuous ell)
    (hell0 : ∀ t, 0 ≤ ell t)
    (hbound : ∀ r ∈ Ioc (1 / 2 : ℝ) 1, ∀ t ∈ Ioo (-Real.pi) Real.pi,
      r * m60AreaDensity g f (r • Proofs.M58.angularPoint t) ≤ K * ell t) :
    (∫ z in (closedBall (0 : LoopPlane) (1 / 2 : ℝ))ᶜ ∩ loopDiskSet,
      m60AreaDensity g f z) ≤ K * ∫ t in Ioo (-Real.pi) Real.pi, ell t := by
  classical
  let A := (closedBall (0 : LoopPlane) (1 / 2 : ℝ))ᶜ
  let S := Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  let Q := Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi
  have hA : MeasurableSet A := measurableSet_closedBall.compl
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioo
  have hSQ : S ⊆ Q := prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self
  have hright : IntegrableOn (fun p : ℝ × ℝ => K * ell p.2) S volume :=
    ((continuous_const.mul (hell.comp continuous_snd)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hSQ
  have hnonneg : ∀ᵐ p ∂volume.restrict S,
      0 ≤ p.1 * A.indicator (m60AreaDensity g f) (p.1 • Proofs.M58.angularPoint p.2) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact mul_nonneg hp.1.1.le (indicator_nonneg (fun z _ => m60AreaDensity_nonneg g f z) _)
  have hle : ∀ᵐ p ∂volume.restrict S,
      p.1 * A.indicator (m60AreaDensity g f) (p.1 • Proofs.M58.angularPoint p.2) ≤ K * ell p.2 := by
    filter_upwards [ae_restrict_mem hS] with p hp
    have hnorm : ‖p.1 • Proofs.M58.angularPoint p.2‖ = p.1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1.1, Proofs.M58.norm_angularPoint, mul_one]
    by_cases hmem : p.1 • Proofs.M58.angularPoint p.2 ∈ A
    · rw [indicator_of_mem hmem]
      have hr : (1 / 2 : ℝ) < p.1 := by
        simpa only [A, mem_compl_iff, mem_closedBall, dist_zero_right, hnorm, not_le] using hmem
      exact hbound p.1 ⟨hr, hp.1.2⟩ p.2 hp.2
    · rw [indicator_of_notMem hmem, mul_zero]
      exact mul_nonneg hK (hell0 p.2)
  have hid : (∫ z in A ∩ loopDiskSet, m60AreaDensity g f z) =
      ∫ z in loopDiskSet, A.indicator (m60AreaDensity g f) z := by
    rw [integral_indicator hA, Measure.restrict_restrict hA]
  rw [hid, Proofs.M58.integral_loopDisk_polar]
  calc
    _ ≤ ∫ p in S, K * ell p.2 := integral_mono_of_nonneg hnonneg hright hle
    _ = K * ∫ t in Ioo (-Real.pi) Real.pi, ell t := by
      change (∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        (fun _ : ℝ => K) p.1 * ell p.2 ∂volume.prod volume) = _
      rw [setIntegral_prod_mul (fun _ : ℝ => K) ell (Ioc (0 : ℝ) 1) (Ioo (-Real.pi) Real.pi)]
      simp

end PoincareConjecture
