import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.SliceChart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.SliceDensity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChangeOfVariables

set_option autoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace
open Poincare.EuclideanSpace Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
  (c : ℝ)

local instance coarea_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1))) M)
  (heU : e.target ⊆ U) (hef : ∀ y ∈ e.source, f (e y) = y 0)

theorem pullbackVolumeDensity_regularLevel_sliceChart
    (z₀ : openLevelSet f U c)
    (he : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e e.source)
    {y : EuclideanSpace ℝ (Fin n)} (hy : euclideanCons c y ∈ e.source) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    (regularLevelMetric hf U hreg c g).pullbackVolumeDensity
      (sliceChart U c e heU hef z₀) y =
      g.levelCoordinateDensity e (euclideanCons c y) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  have hs := contMDiffOn_sliceChart U c e heU hef z₀ hf hreg he
  have hsy := hs.contMDiffAt
    ((sliceChart U c e heU hef z₀).open_source.mem_nhds hy)
  change pullbackVolumeDensity (Induced.pullbackMetric g (openLevelIncl f U c)
    (contMDiff_openLevelIncl hf U hreg n c)
    (injective_mfderiv_openLevelIncl hf U hreg n c))
    (sliceChart U c e heU hef z₀) y = _
  rw [pullbackVolumeDensity_induced g _ _ _ (hsy.mdifferentiableAt (by simp))]
  have heq : (openLevelIncl f U c ∘ sliceChart U c e heU hef z₀) =ᶠ[𝓝 y]
      (e ∘ euclideanCons c) := by
    filter_upwards [((sliceChart U c e heU hef z₀).open_source.mem_nhds hy)] with z hz
    exact sliceChart_apply U c e heU hef z₀ hz
  rw [g.parametrizedVolumeDensity_congr heq]
  exact g.parametrizedVolumeDensity_slice
    ((he.contMDiffAt (e.open_source.mem_nhds hy)).mdifferentiableAt (by simp))

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

noncomputable def regularLevelVolume : Measure (openLevelSet f U c) := by
  letI := openLevelSetChartedSpace hf U hreg n c
  letI := isManifold_openLevelSet hf U hreg n c
  exact (regularLevelMetric hf U hreg c g).volumeMeasure

include heU hef in

theorem integral_regularLevel_sliceChart
    (z₀ : openLevelSet f U c)
    (he : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e.symm e.target)
    {h : M → ℝ} (hh : ContinuousOn h e.target) :
    (∫ z in openLevelIncl f U c ⁻¹' e.target,
      h (openLevelIncl f U c z) ∂g.regularLevelVolume hf U hreg c) =
    ∫ y in euclideanCons c ⁻¹' e.source,
      h (e (euclideanCons c y)) * g.levelCoordinateDensity e (euclideanCons c y) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  have hs := contMDiffOn_sliceChart U c e heU hef z₀ hf hreg he
  have hsi := contMDiffOn_sliceChart_symm U c e heU hef z₀ hf hreg hei
  have hhc : ContinuousOn (h ∘ openLevelIncl f U c)
      (sliceChart U c e heU hef z₀).target :=
    hh.comp (continuous_subtype_val.comp continuous_subtype_val).continuousOn
      (fun _ hz => hz)
  have hc := (regularLevelMetric hf U hreg c g).integral_target_eq_integral_pullback_density
    (sliceChart U c e heU hef z₀) hs hsi hhc
  change (∫ z in (sliceChart U c e heU hef z₀).target,
      (h ∘ openLevelIncl f U c) z ∂(regularLevelMetric hf U hreg c g).volumeMeasure) = _
  rw [hc]
  apply setIntegral_congr_fun (sliceChart U c e heU hef z₀).open_source.measurableSet
  intro y hy
  exact congrArg₂ (fun a b : ℝ => a * b)
    (congrArg h (sliceChart_apply U c e heU hef z₀ hy))
    (g.pullbackVolumeDensity_regularLevel_sliceChart hf U hreg c e heU hef z₀ he hy)

include heU hef in

theorem integral_regularLevel_chart
    (he : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e.symm e.target)
    {h : M → ℝ} (hh : ContinuousOn h e.target) :
    (∫ z in openLevelIncl f U c ⁻¹' e.target,
      h (openLevelIncl f U c z) ∂g.regularLevelVolume hf U hreg c) =
    ∫ y in euclideanCons c ⁻¹' e.source,
      h (e (euclideanCons c y)) * g.levelCoordinateDensity e (euclideanCons c y) := by
  rcases isEmpty_or_nonempty (openLevelSet f U c) with hL | hL
  · let := hL
    have hs : euclideanCons c ⁻¹' e.source = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hL.false ⟨⟨e (euclideanCons c y), heU (e.map_source hy)⟩,
        by
          change f (e (euclideanCons c y)) = c
          simpa only [euclideanCons_zero] using hef _ hy⟩
    simp [hs, integral_of_isEmpty]
  · obtain ⟨z₀⟩ := hL
    exact g.integral_regularLevel_sliceChart hf U hreg c e heU hef z₀ he hei hh

include heU hef in

theorem integral_regularLevel_of_support_subset
    (he : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e.symm e.target)
    {h : M → ℝ} (hh : ContinuousOn h e.target)
    (hs : Function.support h ⊆ e.target) :
    (∫ z, h (openLevelIncl f U c z) ∂g.regularLevelVolume hf U hreg c) =
    ∫ y in euclideanCons c ⁻¹' e.source,
      h (e (euclideanCons c y)) * g.levelCoordinateDensity e (euclideanCons c y) := by
  rw [← g.integral_regularLevel_chart hf U hreg c e heU hef he hei hh]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact Function.notMem_support.mp (fun hh => hz (hs hh))

end PoincareConjecture.RiemannianMetric
