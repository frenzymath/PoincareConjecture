import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.FactorFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.Factor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.FactorRatio
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.Noncollapse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

open RiemannianMetric

theorem parallelGradientFactor_ancient_geometry
    {n : ℕ} (hn : 0 < n) {M : Type u}
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (n + 1) M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ∀ t ≤ 0, HasUnitGradient (F.connection t) f)
    (hz : ∀ t ≤ 0, HasZeroHessian (F.connection t) f)
    (p : M) (hscalar : 0 < (F.connection 0).scalarCurvature p)
    (hvolume : 0 < (F.metric 0).asymptoticVolumeRatio p) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient (hu 0 le_rfl) x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient (hu 0 le_rfl) x) n 0
    let H := F.parallelGradientFactor hf (show (0 : ℝ) ∈ Iic 0 by simp) hu hz
    let κ := (F.metric 0).asymptoticVolumeRatio p / 2 ^ (n + 2)
    0 < κ ∧ Nonempty (zeroLevelSet f) ∧ ConnectedSpace (zeroLevelSet f) ∧
      NoncompactSpace (zeroLevelSet f) ∧
      (∀ t ≤ 0, MetricComplete (H.metric t)) ∧
      (∀ t ≤ 0, ∀ y, (H.connection t).NonnegativeCurvatureOperator y) ∧
      (∀ t ≤ 0, ∀ y, (H.connection t).curvatureTensorNorm y ≤ K) ∧
      (∃ y, 0 < (H.connection 0).scalarCurvature y ∧
        0 < (H.metric 0).asymptoticVolumeRatio y) ∧
      (∀ t ≤ 0, ∀ y, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (κ * r ^ n) ≤ (H.metric t).volumeMeasure ((H.metric t).ball y r)) ∧
      (∀ t ≤ 0, ∀ y, ∀ r : ℝ, 0 < r →
        (∀ s ∈ Icc (t - r ^ 2) t, ∀ z ∈ (H.metric t).ball y r,
          (H.connection s).curvatureTensorNorm z ≤ r⁻¹ ^ 2) →
        ENNReal.ofReal (κ * r ^ n) ≤ (H.metric t).volumeMeasure ((H.metric t).ball y r)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient (hu 0 le_rfl) x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let H := F.parallelGradientFactor hf (show (0 : ℝ) ∈ Iic 0 by simp) hu hz
  let κ := (F.metric 0).asymptoticVolumeRatio p / 2 ^ (n + 2)
  have hκ : 0 < κ := div_pos hvolume (by positivity)
  have hRic (t : ℝ) (ht : t ≤ 0) (x : M) (v : TangentSpace (𝓡 (n + 1)) x) :
      0 ≤ (F.connection t).ricci x v v :=
    ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (n + 1) M (F.metric t) (F.connection t)) x (hop t ht x) v).1
  obtain ⟨hne, hconn, hcomplete, hoperator, hnorm, hnonflat⟩ :=
    F.parallelGradientFactor_geometry hf (show (0 : ℝ) ∈ Iic 0 by simp)
      hu hz hc hop hbound
  have hnoncompact := noncompact_parallelGradient_factor_of_asymptoticVolumeRatio hn
    (hc 0 le_rfl) (hRic 0 le_rfl) hf (hu 0 le_rfl) (hz 0 le_rfl) p hvolume
  have hfactorVolume := parallelGradient_factor_volume_bounds_of_asymptoticVolumeRatio hn
    (hc 0 le_rfl) (hRic 0 le_rfl) hf (hu 0 le_rfl) (hz 0 le_rfl) p hvolume
  have hballs : ∀ t ≤ 0, ∀ y, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (κ * r ^ n) ≤ (H.metric t).volumeMeasure ((H.metric t).ball y r) := by
    intro t ht
    have ha := F.ancient_ball_volume_lower_bound_of_terminal_asymptoticVolumeRatio
      hC hn hc hop hK hbound p hvolume t ht
    have hb := parallelGradient_factor_volume_bounds_of_ball_volume_lower_bound hn
      (hc t ht) (hRic t ht) hf (hu t ht) (hz t ht)
      (div_pos hvolume (by positivity : 0 < (2 : ℝ) ^ (n + 1))) ha
    have heq : ((F.metric 0).asymptoticVolumeRatio p / 2 ^ (n + 1)) / 2 = κ := by
      dsimp only [κ]
      simp only [div_div, show n + 2 = (n + 1) + 1 by omega, pow_succ]
    intro y r hr
    simpa only [heq, H, parallelGradientFactor] using hb.2.1 y r hr
  refine ⟨hκ, hne, hconn, hnoncompact, hcomplete, hoperator, hnorm, ?_, hballs, ?_⟩
  · obtain ⟨y, hy⟩ := hnonflat 0 (by simp) p hscalar
    exact ⟨y, hy, hfactorVolume.2.2.2 y⟩
  · intro t ht y r hr _
    exact hballs t ht y r hr

end PoincareConjecture.RicciFlow
