import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Degenerate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

omit [PreconnectedSpace M] in
theorem hasDerivAt_deriv_potential_geodesic (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {γ : ℝ → M} {I : Set ℝ} (hgeo : g.IsGeodesicOn γ I)
    {C t : ℝ} (ht : t ∈ I)
    (hspeed : g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = C) :
    HasDerivAt (deriv (f ∘ γ))
      ((lambda - D.scalarCurvature (γ t) / 2) * C ^ 2) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn isOpen_univ
    (D.contMDiff_of_C2_surface_soliton hf hsol).contMDiffOn hgeo ht (mem_univ _)
  rw [D.hessian_eq_of_surface_soliton hsol] at hs
  have hnorm : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = C ^ 2 := by
    have hnonneg : 0 ≤ g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) := by
      change 0 ≤ inner ℝ (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
      exact real_inner_self_nonneg
    have hh := congrArg (fun r : ℝ => r ^ 2) hspeed
    rwa [RiemannianMetric.tangentNorm, Real.sq_sqrt hnonneg] at hh
  rw [hnorm] at hs
  convert hs using 1
  ring

theorem hasDerivAt_second_deriv_potential_geodesic (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {γ : ℝ → M} {I : Set ℝ} (hI : IsOpen I) (hgeo : g.IsGeodesicOn γ I)
    {C : ℝ} (hspeed : ∀ s ∈ I,
      g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ s 1) = C)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (deriv (deriv (f ∘ γ)))
      (-(D.scalarCurvature (γ t) * C ^ 2 / 2) * deriv (f ∘ γ) t) t := by
  have hf1 : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 1 f := hf.of_le (by norm_num)
  have hF : HasDerivAt (f ∘ γ) (deriv (f ∘ γ) t) t := by
    apply DifferentiableAt.hasDerivAt
    exact (contMDiffAt_iff_contDiffAt.mp ((hf1 (γ t)).comp t
      (hgeo.contMDiffAt ht))).differentiableAt (by simp)
  have heq : deriv (deriv (f ∘ γ)) =ᶠ[𝓝 t] fun s =>
      (lambda - D.scalarCurvature (γ t) / 2 * Real.exp (f (γ s) - f (γ t))) * C ^ 2 := by
    filter_upwards [hI.mem_nhds ht] with s hs
    rw [(D.hasDerivAt_deriv_potential_geodesic hf hsol hgeo hs (hspeed s hs)).deriv,
      D.scalar_eq_exp_potential_difference_of_surface_soliton hf hsol (γ t) (γ s)]
    ring
  have hexp := ((hF.sub_const (f (γ t))).exp).const_mul (D.scalarCurvature (γ t) / 2)
  have hd := (hexp.const_sub lambda).mul_const (C ^ 2)
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  simp only [Function.comp_apply, sub_self, Real.exp_zero]
  ring

end PoincareConjecture.LeviCivitaData
