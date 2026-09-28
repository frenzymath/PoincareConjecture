import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.FactorFlow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

namespace RiemannianMetric

theorem parallelGradient_factor_kappaNoncollapsed
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] {g : RiemannianMetric (n + 1) M}
    {D : LeviCivitaData g} {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f)
    {κ : ℝ} (hκ : MetricKappaNoncollapsed g D κ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    MetricKappaNoncollapsed h h.leviCivitaData (κ / 2) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  obtain ⟨_, hconn, _, Φ, e, _, _, _, _, hm, _, hnorm, _⟩ :=
    exists_parallelGradient_productIsometry_curvature hc hf hu hz
  let : ConnectedSpace (zeroLevelSet f) := hconn
  let : SecondCountableTopology (zeroLevelSet f) := h.secondCountableTopology
  refine ⟨div_pos hκ.1 (by norm_num), fun y r hr hcurv => ?_⟩
  rw [calibratedMetricVolume_eq_volumeMeasure]
  apply volumeMeasure_factor_lower_bound h g e hm y r κ hr
  rw [← calibratedMetricVolume_eq_volumeMeasure]
  apply hκ.2 (e (y, 0)) r hr
  intro x hx
  rw [← hnorm x]
  apply hcurv (e.symm x).1
  change h.edist y (e.symm x).1 < ENNReal.ofReal r
  change g.edist (e (y, 0)) x < ENNReal.ofReal r at hx
  have hproj := productIsometry_fst_edist_le g h e hm (e (y, 0)) x
  simpa only [e.symm_apply_apply] using hproj.trans_lt hx

end RiemannianMetric

namespace RicciFlow

open RiemannianMetric

theorem parallelGradientFactor_kappaNoncollapsed
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] {J : Set ℝ}
    (F : RicciFlow (n + 1) M J)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hu : ∀ t ∈ J, HasUnitGradient (F.connection t) f)
    (hz : ∀ t ∈ J, HasZeroHessian (F.connection t) f)
    (hc : ∀ t ∈ J, MetricComplete (F.metric t))
    {κ : ℝ} (hκ : ∀ t ∈ J, MetricKappaNoncollapsed (F.metric t) (F.connection t) κ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient (hu t₀ ht₀) x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient (hu t₀ ht₀) x) n 0
    let H := F.parallelGradientFactor hf ht₀ hu hz
    ∀ t ∈ J, MetricKappaNoncollapsed (H.metric t) (H.connection t) (κ / 2) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient (hu t₀ ht₀) x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  dsimp only
  intro t ht
  exact parallelGradient_factor_kappaNoncollapsed (hc t ht) hf (hu t ht) (hz t ht) (hκ t ht)

end RicciFlow

end PoincareConjecture
