import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Noncollapse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

theorem noncompactSpace_of_ball_volume_lower_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hn : 0 < n) (p : M)
    {κ : ℝ} (hκ : 0 < κ)
    (hvolume : ∀ r : ℝ, 0 < r → ENNReal.ofReal (κ * r ^ n) ≤
      g.volumeMeasure (g.ball p r)) : NoncompactSpace M := by
  apply not_compactSpace_iff.mp
  intro hcompact
  let : CompactSpace M := hcompact
  have hfinite : g.volumeMeasure univ ≠ ⊤ :=
    (g.volumeMeasure_lt_top_of_isCompact isCompact_univ).ne
  have htendsto : Tendsto (fun r : ℝ => κ * r ^ n) atTop atTop :=
    Tendsto.const_mul_atTop hκ (tendsto_pow_atTop hn.ne')
  obtain ⟨r, hr, hlarge⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (htendsto.eventually_gt_atTop (g.volumeMeasure univ).toReal)).exists
  have hsmall := ENNReal.toReal_mono hfinite
    ((hvolume r hr).trans (measure_mono (subset_univ _)))
  rw [ENNReal.toReal_ofReal (mul_nonneg hκ.le (pow_nonneg hr.le n))] at hsmall
  exact (not_le_of_gt hlarge) hsmall

theorem noncompact_parallelGradient_factor_of_asymptoticVolumeRatio
    {n : ℕ} (hn : 0 < n) {M : Type*}
    [TopologicalSpace M] [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {g : RiemannianMetric (n + 1) M} {D : LeviCivitaData g}
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 (n + 1)) x, 0 ≤ D.ricci x v v)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f)
    (p : M) (hvolume : 0 < g.asymptoticVolumeRatio p) :
    NoncompactSpace (zeroLevelSet f) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  obtain ⟨hne, _, _, Φ, e, _, _, _, _, _, _, hlower⟩ :=
    exists_parallelGradient_volumeSplitting hc hf hu hz
  let κ := g.asymptoticVolumeRatio p / 2 ^ (n + 1)
  have hκ : 0 < κ := div_pos hvolume (by positivity)
  have hfactor : ∀ y r, 0 < r →
      ENNReal.ofReal ((κ / 2) * r ^ n) ≤ h.volumeMeasure (h.ball y r) := by
    apply hlower κ hκ
    intro y r hr
    exact g.ball_volume_lower_bound_of_asymptoticVolumeRatio D (by omega) hc hRic
      p (e (y, 0)) (g.edist_ne_top p (e (y, 0))) hvolume.le hr le_rfl
  exact h.noncompactSpace_of_ball_volume_lower_bound hn (Classical.choice hne)
    (div_pos hκ (by norm_num)) (hfactor _)

end PoincareConjecture.RiemannianMetric
