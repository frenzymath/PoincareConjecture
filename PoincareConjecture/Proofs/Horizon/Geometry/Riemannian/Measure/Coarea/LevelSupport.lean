import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.LevelVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite

set_option autoImplicit false

open Set Function MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

theorem hasCompactSupport_openLevelIncl
    {M : Type*} [TopologicalSpace M] [T2Space M]
    {f : M → ℝ} (hf : Continuous f) (U : Opens M) (c : ℝ)
    {h : M → ℝ} (hh : HasCompactSupport h) (hU : tsupport h ⊆ U) :
    HasCompactSupport (h ∘ openLevelIncl f U c) := by
  have hcompact : IsCompact (openLevelIncl f U c ⁻¹' tsupport h) := by
    apply (isEmbedding_openLevelIncl f U c).isCompact_iff.mpr
    rw [image_preimage_eq_inter_range, range_openLevelIncl]
    have hset : tsupport h ∩ ((U : Set M) ∩ f ⁻¹' {c}) = tsupport h ∩ f ⁻¹' {c} := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hU hx.1, hx.2⟩⟩
    rw [hset]
    exact hh.isCompact.inter_right (isClosed_singleton.preimage hf)
  exact HasCompactSupport.of_support_subset_isCompact hcompact
    (fun _ hz => subset_tsupport h hz)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
  (c : ℝ)

local instance levelSupport_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem integrable_regularLevelVolume_of_hasCompactSupport
    {h : M → ℝ} (hh : Continuous h) (hcompact : HasCompactSupport h)
    (hU : tsupport h ⊆ U) :
    Integrable (h ∘ openLevelIncl f U c) (g.regularLevelVolume hf U hreg c) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  exact (regularLevelMetric hf U hreg c g).integrable_volumeMeasure_of_hasCompactSupport
    (hh.comp (continuous_subtype_val.comp continuous_subtype_val))
    (hasCompactSupport_openLevelIncl hf.continuous U c hcompact hU)

end PoincareConjecture.RiemannianMetric
