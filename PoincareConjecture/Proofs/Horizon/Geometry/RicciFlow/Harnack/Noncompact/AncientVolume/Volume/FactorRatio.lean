import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.AsymptoticRatio
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Noncollapse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M} {D : LeviCivitaData g}

theorem parallelGradient_factor_volume_bounds_of_ball_volume_lower_bound
    (hn : 0 < n) (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 (n + 1)) x, 0 ≤ D.ricci x v v)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f)
    {κ : ℝ} (hκ : 0 < κ)
    (hvolume : ∀ x : M, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (κ * r ^ (n + 1)) ≤ g.volumeMeasure (g.ball x r)) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    (∀ y : zeroLevelSet f, ∀ v : TangentSpace (𝓡 n) y,
      0 ≤ h.leviCivitaData.ricci y v v) ∧
    (∀ y : zeroLevelSet f, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal ((κ / 2) * r ^ n) ≤ h.volumeMeasure (h.ball y r)) ∧
    ∀ y : zeroLevelSet f, κ / 2 ≤ h.asymptoticVolumeRatio y := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  obtain ⟨_, hconn, hcomplete, Φ, e, _, _, _, _, _, _, hlower⟩ :=
    exists_parallelGradient_volumeSplitting hc hf hu hz
  let : ConnectedSpace (zeroLevelSet f) := hconn
  have hfactorRic : ∀ y : zeroLevelSet f, ∀ v : TangentSpace (𝓡 n) y,
      0 ≤ h.leviCivitaData.ricci y v v := by
    intro y v
    rw [(parallelGradient_factor_curvature hf hu hz y).2.2.1]
    exact hRic _ _
  have hfactorVolume : ∀ y : zeroLevelSet f, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal ((κ / 2) * r ^ n) ≤ h.volumeMeasure (h.ball y r) :=
    hlower κ hκ (fun y r hr => hvolume (e (y, 0)) r hr)
  refine ⟨hfactorRic, hfactorVolume, ?_⟩
  intro y
  exact h.le_asymptoticVolumeRatio_of_ball_volume_lower_bound h.leviCivitaData hn
    hcomplete hfactorRic y (div_nonneg hκ.le (by norm_num)) (hfactorVolume y)

theorem parallelGradient_factor_volume_bounds_of_asymptoticVolumeRatio
    (hn : 0 < n) (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 (n + 1)) x, 0 ≤ D.ricci x v v)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f)
    (p : M) (hvolume : 0 < g.asymptoticVolumeRatio p) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    let κ := g.asymptoticVolumeRatio p / 2 ^ (n + 2)
    (∀ y : zeroLevelSet f, ∀ v : TangentSpace (𝓡 n) y,
      0 ≤ h.leviCivitaData.ricci y v v) ∧
    (∀ y : zeroLevelSet f, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (κ * r ^ n) ≤ h.volumeMeasure (h.ball y r)) ∧
    (∀ y : zeroLevelSet f, κ ≤ h.asymptoticVolumeRatio y) ∧
    ∀ y : zeroLevelSet f, 0 < h.asymptoticVolumeRatio y := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  let κ := g.asymptoticVolumeRatio p / 2 ^ (n + 1)
  have hκ : 0 < κ := div_pos hvolume (by positivity)
  have hvolume' (x : M) (r : ℝ) (hr : 0 < r) :
      ENNReal.ofReal (κ * r ^ (n + 1)) ≤ g.volumeMeasure (g.ball x r) :=
    g.ball_volume_lower_bound_of_asymptoticVolumeRatio D (by omega) hc hRic
      p x (g.edist_ne_top p x) hvolume.le hr le_rfl
  obtain ⟨hRic', hball, hratio⟩ :=
    parallelGradient_factor_volume_bounds_of_ball_volume_lower_bound hn hc hRic hf hu hz hκ hvolume'
  have heq : κ / 2 = g.asymptoticVolumeRatio p / 2 ^ (n + 2) := by
    dsimp only [κ]
    simp only [div_div, show n + 2 = (n + 1) + 1 by omega, pow_succ]
  refine ⟨hRic', ?_, ?_, ?_⟩
  · simpa only [heq] using hball
  · simpa only [heq] using hratio
  · intro y
    exact (div_pos hκ (by norm_num)).trans_le (hratio y)

end PoincareConjecture.RiemannianMetric
