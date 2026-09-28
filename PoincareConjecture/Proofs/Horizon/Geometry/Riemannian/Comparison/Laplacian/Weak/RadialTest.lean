import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Weak.RadialIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]



theorem exists_contDiff_radial_test {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (θ : EuclideanSpace ℝ (Fin n)) (hθ : ‖θ‖ = 1) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      ∀ t ∈ Icc (0 : ℝ) r, f =ᶠ[𝓝 t] (fun s => φ (e (s • θ))) := by
  let a := (r + R) / 2
  let b := (a + R) / 2
  have hra : r < a := by dsimp [a]; linarith
  have haR : a < R := by dsimp [a]; linarith
  have hab : a < b := by dsimp [b]; linarith
  have hbR : b < R := by dsimp [b]; linarith
  let χ : ContDiffBump (0 : ℝ) := ⟨a, b, hr.trans hra, hab⟩
  let F := fun t : ℝ => φ (e (t • θ))
  have hparam : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun t : ℝ => t • θ) :=
    (contDiff_id.smul contDiff_const).contMDiff
  have hF : ContDiffOn ℝ ∞ F (Metric.ball 0 R) := by
    intro t ht
    have htball : t • θ ∈ Metric.ball 0 R := by
      rw [mem_ball_zero_iff, norm_smul, hθ, mul_one]
      exact mem_ball_zero_iff.mp ht
    have hcomp := (hφ (e (t • θ))).comp t
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds htball)).comp t (hparam t))
    exact hcomp.contDiffAt.contDiffWithinAt
  have hsupp : tsupport χ ⊆ Metric.ball 0 R := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball hbR
  have hcutoff : ContDiff ℝ ∞ (fun t => χ t * F t) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t ∈ tsupport χ
    · exact χ.contDiffAt.mul (hF.contDiffAt (Metric.isOpen_ball.mem_nhds (hsupp ht)))
    · apply contDiffAt_const.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℝ))
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with s hs
      simp [hs]
  refine ⟨fun t => χ t * F t, hcutoff, χ.hasCompactSupport.mul_right, ?_⟩
  intro t ht
  have hta : t ∈ Metric.ball (0 : ℝ) χ.rIn := by
    rw [mem_ball_zero_iff, Real.norm_of_nonneg ht.1]
    exact ht.2.trans_lt hra
  filter_upwards [χ.eventuallyEq_one_of_mem_ball hta] with s hs
  simp only [hs, Pi.one_apply, one_mul, F]

end Poincare.Manifold

namespace PoincareConjecture.RiemannianMetric

open Poincare.VolumeComparison

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]



theorem radial_integral_laplacian_comparison_test
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {p : M} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    {L : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))}
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 (m + 1)) p).symm
      (extChartAt (𝓡 (m + 1)) p p) (L v) (L w) = inner ℝ v w)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Metric.ball 0 R))
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 (m + 1)) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t | t • v ∈ Metric.ball 0 R} ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (e (t • v))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun s : ℝ => e (s • v)) t 1) = ‖v‖ ∧
        g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 (m + 1)) x, 0 ≤ D.ricci x v v)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    let S := localMinimizingSet (fun v => g.edist p (e v)) R
    let H := fun t : ℝ => (S \ terminalRadialPoints S R).indicator
      (g.pullbackVolumeDensity e) (t • (θ : EuclideanSpace ℝ (Fin (m + 1))));
    -(∫ t in Ioo (0 : ℝ) r, (t ^ m * H t) *
      deriv (fun s => φ (e (s • (θ : EuclideanSpace ℝ (Fin (m + 1)))))) t) ≤
      ∫ t in Ioo (0 : ℝ) r, (m : ℝ) / t *
        φ (e (t • (θ : EuclideanSpace ℝ (Fin (m + 1))))) * (t ^ m * H t) := by
  obtain ⟨f, hf, _, heq⟩ := Poincare.Manifold.exists_contDiff_radial_test hr hrR he hφ
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (mem_sphere_zero_iff_norm.mp θ.property)
  have hfpos : ∀ t ∈ Icc (0 : ℝ) r, 0 ≤ f t := by
    intro t ht
    rw [(heq t ht).self_of_nhds]
    exact hφ0 _
  have h := g.radial_integral_laplacian_comparison D hm hr hrR hL he he0 hed hgeo hRic θ
    (hf.of_le (by norm_num)) hfpos
  dsimp only at h ⊢
  convert h using 1
  · congr 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [(heq t ⟨ht.1.le, ht.2.le⟩).deriv_eq]
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [(heq t ⟨ht.1.le, ht.2.le⟩).self_of_nhds]

end PoincareConjecture.RiemannianMetric
