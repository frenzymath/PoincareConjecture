import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Variation.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeMeasure
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {J : Set ℝ}

theorem hasDerivAt_integral_volumeMeasure_image_surface
    (F : RicciFlow 2 M J) {t : ℝ} (ht : t ∈ interior J)
    {u : ℝ → M → ℝ}
    (hu : ∀ s ∈ interior J, ∀ y : M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => u p.1 p.2) (s, y))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {K L : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L) (hLe : L ⊆ e.source) :
    HasDerivAt (fun s => ∫ y in e '' K, u s y ∂(F.metric s).volumeMeasure)
      (∫ y in e '' K, deriv (fun s => u s y) t -
        (F.connection t).scalarCurvature y * u t y ∂(F.metric t).volumeMeasure) t := by
  have hus (s : ℝ) (hs : s ∈ interior J) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (u s) := by
    intro x
    exact (hu s hs x).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  have hdt : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => deriv (fun s => u s x) t) := by
    intro x
    exact (Poincare.Manifold.contMDiffAt_deriv_time (hu t ht x)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hw : Continuous (fun x => deriv (fun s => u s x) t -
      (F.connection t).scalarCurvature x * u t x) :=
    hdt.continuous.sub ((F.connection t).continuous_scalarCurvature.mul (hus t ht).continuous)
  have heD : e.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hd := F.hasDerivAt_integral_weighted_pullbackVolumeDensity_surface ht hu e hK hL hKL
    (fun x hx => he.contMDiffAt (e.open_source.mem_nhds (hLe hx)))
    (fun x hx => heD.mfderiv_injective (hLe hx))
  have hfun : (fun s => ∫ y in e '' K, u s y ∂(F.metric s).volumeMeasure) =ᶠ[𝓝 t]
      (fun s => ∫ x in K, u s (e x) * (F.metric s).pullbackVolumeDensity e x) := by
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    exact (F.metric s).integral_image_eq_integral_pullback_density
      e he hei hK (hKL.trans hLe) (hus s hs).continuous.continuousOn
  apply (hd.congr_of_eventuallyEq hfun).congr_deriv
  exact ((F.metric t).integral_image_eq_integral_pullback_density e he hei
    hK (hKL.trans hLe) hw.continuousOn).symm

end PoincareConjecture.RicciFlow
