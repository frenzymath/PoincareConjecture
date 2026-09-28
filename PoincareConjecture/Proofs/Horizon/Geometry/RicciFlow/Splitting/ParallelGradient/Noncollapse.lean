import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.TerminalFactor

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

open RiemannianMetric

theorem parallelGradientFactor_parabolic_noncollapsed
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (F : RicciFlow (n + 1) M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ∀ t ≤ 0, HasUnitGradient (F.connection t) f)
    (hz : ∀ t ≤ 0, HasZeroHessian (F.connection t) f)
    (hp : ∀ t ≤ 0, (F.connection t).gradient f = (F.connection 0).gradient f)
    {κ : ℝ} (hκ : AncientKappaNoncollapsed F κ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient (hu 0 le_rfl) x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient (hu 0 le_rfl) x) n 0
    AncientKappaNoncollapsed
      (F.parallelGradientFactor hf (show (0 : ℝ) ∈ Iic 0 by simp) hu hz) (κ / 2) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient (hu 0 le_rfl) x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let H := F.parallelGradientFactor hf (show (0 : ℝ) ∈ Iic 0 by simp) hu hz
  intro r₀ hr₀ t ht y r hr hrr hcurv
  obtain ⟨hne, hconn, _, Φ, e, h0, hΦ, he, _, hmetric, _, hnorm, _⟩ :=
    exists_parallelGradient_productIsometry_curvature (hc t ht) hf (hu t ht) (hz t ht)
  let : ConnectedSpace (zeroLevelSet f) := hconn
  let : SecondCountableTopology (zeroLevelSet f) := (H.metric t).secondCountableTopology
  rw [calibratedMetricVolume_eq_volumeMeasure]
  apply volumeMeasure_factor_lower_bound (H.metric t) (F.metric t) e hmetric y r κ hr
  rw [← calibratedMetricVolume_eq_volumeMeasure]
  apply hκ r₀ hr₀ t ht (e (y, 0)) r hr hrr
  intro s hs x hx
  have hs0 : s ≤ 0 := hs.2.trans ht
  obtain ⟨_, _, _, Ψ, d, hΨ0, hΨ, hd, _, _, _, hdnorm, _⟩ :=
    exists_parallelGradient_productIsometry_curvature (hc s hs0) hf (hu s hs0) (hz s hs0)
  have hgrad : (F.connection s).gradient f = (F.connection t).gradient f :=
    (hp s hs0).trans (hp t ht).symm
  have hde : d = e := by
    apply Diffeomorph.ext
    intro z
    rw [hd, he]
    have hcurve := hΨ (zeroLevelIncl f z.1)
    rw [hgrad] at hcurve
    have hsame := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      ((F.connection t).contMDiff_gradient hf |>.of_le (by simp)) hcurve
      (hΦ (zeroLevelIncl f z.1)) (show Ψ 0 (zeroLevelIncl f z.1) = Φ 0 (zeroLevelIncl f z.1) by
        rw [hΨ0, h0])
    exact congrFun hsame z.2
  have hproj : (e.symm x).1 ∈ (H.metric t).ball y r := by
    have hi := productIsometry_preimage_ball_subset (F.metric t) (H.metric t)
      e hmetric y r hr
    exact (hi (show e.symm x ∈ e ⁻¹' (F.metric t).ball (e (y, 0)) r by
      simpa only [mem_preimage, e.apply_symm_apply] using hx)).1
  rw [← hdnorm x, hde]
  exact hcurv s hs (e.symm x).1 hproj

theorem terminalParallelGradientFactor_parabolic_noncollapsed
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 1) M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : HasUnitGradient (F.connection 0) f)
    (hzero : HasZeroHessian (F.connection 0) f)
    {κ : ℝ} (hκ : AncientKappaNoncollapsed F κ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hunit x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hunit x) n 0
    AncientKappaNoncollapsed
      (F.terminalParallelGradientFactor hC hc hop hK hbound hf hunit hzero) (κ / 2) := by
  have hp := F.ancient_backward_persistence_of_parallel_gradient hC (by omega)
    hc hop ⟨K, hK, hbound⟩ f hf hunit hzero
  exact F.parallelGradientFactor_parabolic_noncollapsed hc hf
    (fun t ht => (hp t ht).2.1) (fun t ht => (hp t ht).2.2)
    (fun t ht => (hp t ht).1) hκ

end PoincareConjecture.RicciFlow
