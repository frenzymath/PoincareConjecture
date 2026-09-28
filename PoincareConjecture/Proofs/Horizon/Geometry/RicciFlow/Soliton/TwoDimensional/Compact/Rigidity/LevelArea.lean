import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.GlobalExtrema
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Extrema
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Area
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem levelMeanCurvature_div_speed_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (x : M) (hreg : 0 < D.levelQ f x) :
    D.levelMeanCurvature f x / g.tangentNorm x (g.gradient f x) =
      (lambda - D.scalarCurvature x / 2) / D.levelQ f x := by
  rw [D.levelMeanCurvature_eq_scalarOperators hf x hreg]
  have hcross : g.inner x (D.gradient (D.levelQ f) x) (D.gradient f x) =
      2 * (lambda - (1 / 2 : ℝ) * D.scalarCurvature x) * D.levelQ f x := by
    rw [D.inner_gradient]
    unfold levelQ
    rw [D.mvfderiv_gradient_normSq (hf x),
      D.hessian_eq_of_surface_soliton hsol]
    ring
  rw [hcross]
  have hlap := D.scalar_add_laplacian_of_surface_soliton hsol x
  change (_ / Real.sqrt (D.levelQ f x)) / Real.sqrt (D.levelQ f x) = _
  have hs := Real.sq_sqrt hreg.le
  have hn := (Real.sqrt_pos.mpr hreg).ne'
  field_simp
  rw [hs, show D.laplacian f x = 2 * lambda - D.scalarCurvature x by linarith]
  ring

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem hasDerivAt_regularLevelArea_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {I : Set ℝ} (hI : IsOpen I) (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0)
    {q r : ℝ → ℝ}
    (hQ : ∀ x, f x ∈ I → D.levelQ f x = q (f x))
    (hR : ∀ x, f x ∈ I → D.scalarCurvature x = r (f x))
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (g.regularLevelArea hf)
      ((lambda - r t / 2) / q t * g.regularLevelArea hf t) t := by
  apply ((D.first_variation_regularLevelArea hf hI hproper hreg).2 t ht).congr_deriv
  have heq : (fun z : openLevelSet f (g.regularDomain hf) t =>
      D.levelMeanCurvature f (openLevelIncl f (g.regularDomain hf) t z) /
        g.tangentNorm (openLevelIncl f (g.regularDomain hf) t z)
          (g.gradient f (openLevelIncl f (g.regularDomain hf) t z))) =
      fun _ => (lambda - r t / 2) / q t := by
    funext z
    have hzt : f (openLevelIncl f (g.regularDomain hf) t z) = t := z.2
    have hz : f (openLevelIncl f (g.regularDomain hf) t z) ∈ I := by rw [hzt]; exact ht
    rw [D.levelMeanCurvature_div_speed_of_surface_soliton hf hsol _
      (Real.sqrt_pos.mp ((g.tangentNorm_gradient_pos_iff f _).mpr (hreg _ hz))),
      hQ _ hz, hR _ hz, hzt]
  rw [heq, integral_const]
  simp only [smul_eq_mul, RiemannianMetric.regularLevelArea, mul_comm]

theorem exists_const_regularLevelArea_div_sqrt_of_surface_soliton
    (D : LeviCivitaData g) {f : M → ℝ} {lambda a b : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hproper : IsProperMap ((Ioo a b).restrictPreimage f))
    (hreg : ∀ x, f x ∈ Ioo a b → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0)
    {q r : ℝ → ℝ}
    (hQ : ∀ x, f x ∈ Ioo a b → D.levelQ f x = q (f x))
    (hR : ∀ x, f x ∈ Ioo a b → D.scalarCurvature x = r (f x))
    (hq : ∀ t ∈ Ioo a b, 0 < q t)
    (hqd : ∀ t ∈ Ioo a b, HasDerivAt q (2 * lambda - r t) t) :
    ∃ c : ℝ, ∀ t ∈ Ioo a b,
      g.regularLevelArea hf t / Real.sqrt (q t) = c := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s => g.regularLevelArea hf s / Real.sqrt (q s)) 0 t := by
    have hA := D.hasDerivAt_regularLevelArea_of_surface_soliton hf hsol isOpen_Ioo
      hproper hreg hQ hR ht
    have hs := (hqd t ht).sqrt (hq t ht).ne'
    apply (hA.div hs (Real.sqrt_pos.mpr (hq t ht)).ne').congr_deriv
    have he := Real.sq_sqrt (hq t ht).le
    have hn := (Real.sqrt_pos.mpr (hq t ht)).ne'
    field_simp
    rw [he, div_self (hq t ht).ne']
    ring
  exact isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv)

end PoincareConjecture.LeviCivitaData
