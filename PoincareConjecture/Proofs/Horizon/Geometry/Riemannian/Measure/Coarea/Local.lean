import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.LevelVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Integrability







set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open Poincare.Coarea Poincare.EuclideanSpace Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1))) M)
  (heU : e.target ⊆ U) (hef : ∀ y ∈ e.source, f (e y) = y 0)
  (he : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e.symm e.target)
  {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
  (hs : tsupport h ⊆ e.target)

include hf hef he hei in
omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

lemma levelCoordinateDensity_eq_mul_gradient_norm
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ e.source) :
    g.levelCoordinateDensity e x =
      g.pullbackVolumeDensity e x * g.tangentNorm (e x) (g.gradient f (e x)) := by
  have hD : e.MDifferentiable (𝓡 (n + 1)) (𝓡 (n + 1)) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  exact (g.pullbackVolumeDensity_mul_gradient_norm
    (hD.mdifferentiableAt hx) ((hf (e x)).mdifferentiableAt (by simp))
    (hD.mfderiv_bijective hx)
    (Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hx) (fun y hy => hef y hy))).symm

include hf hef he hei hh hc hs in

theorem integrableOn_levelCoordinateDensity :
    IntegrableOn (fun x => h (e x) * g.levelCoordinateDensity e x) e.source := by
  have hi := g.integrableOn_pullbackVolumeDensity e he hei
    (hh.mul (g.continuous_tangentNorm_gradient hf)) hc.mul_right
    (tsupport_mul_subset_left.trans hs)
  apply hi.congr_fun _ e.open_source.measurableSet
  intro x hx
  dsimp only [Pi.mul_apply]
  rw [g.levelCoordinateDensity_eq_mul_gradient_norm hf e hef he hei hx]
  ring

include heU hef he hei hh hc hs in


theorem integrable_regularLevelIntegral_of_chart_support :
    Integrable (fun c : ℝ => ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c) := by
  have hi := g.integrableOn_levelCoordinateDensity hf e hef he hei hh hc hs
  have hF := integrable_setIntegral_euclideanCons e.open_source.measurableSet hi
  apply hF.congr
  filter_upwards [] with c
  exact (g.integral_regularLevel_of_support_subset hf U hreg c e heU hef he hei
    hh.continuousOn ((subset_tsupport h).trans hs)).symm

include heU hef he hei hh hc hs in


theorem integral_coarea_of_chart_support :
    (∫ x, h x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
    ∫ c : ℝ, ∫ z, h (openLevelIncl f U c z) ∂g.regularLevelVolume hf U hreg c := by
  have hi := g.integrableOn_levelCoordinateDensity hf e hef he hei hh hc hs
  calc
    (∫ x, h x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
        ∫ x in e.target, h x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), zero_mul]
    _ = ∫ x in e.source,
        (h (e x) * g.tangentNorm (e x) (g.gradient f (e x))) *
          g.pullbackVolumeDensity e x :=
      g.integral_target_eq_integral_pullback_density e he hei
        (hh.mul (g.continuous_tangentNorm_gradient hf)).continuousOn
    _ = ∫ x in e.source, h (e x) * g.levelCoordinateDensity e x := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x hx
      dsimp only
      rw [g.levelCoordinateDensity_eq_mul_gradient_norm hf e hef he hei hx]
      ring
    _ = ∫ c : ℝ, ∫ y in euclideanCons c ⁻¹' e.source,
        h (e (euclideanCons c y)) * g.levelCoordinateDensity e (euclideanCons c y) :=
      setIntegral_eq_integral_euclideanCons e.open_source.measurableSet hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with c
      exact (g.integral_regularLevel_of_support_subset hf U hreg c e heU hef he hei
        hh.continuousOn ((subset_tsupport h).trans hs)).symm

end PoincareConjecture.RiemannianMetric
