import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Geodesic.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Chart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hasDerivAt_deriv_comp_geodesic_eq_zero
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M} {s : Set ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hzero : HasZeroHessian D f)
    (hγ : g.IsGeodesicOn γ s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (deriv (f ∘ γ)) 0 t := by
  obtain ⟨p, q, w, hlocal⟩ := hγ t ht
  let c := extChartAt (𝓡 n) p
  let F := f ∘ c.symm
  have hF (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ c.target) :
      ContDiffAt ℝ ∞ F x := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (hf (c.symm x)).comp x
      ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hx).contMDiffAt
        (extChartAt_target_mem_nhds' hx))
  have hfirst : ∀ᶠ u in 𝓝 t,
      HasDerivAt (f ∘ γ) (fderiv ℝ F (q u) (w u)) u := by
    filter_upwards [hlocal, hlocal.eventually_nhds] with u hu hue
    have hd := ((hF (q u) hu.2.1).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt u hu.2.2.1
    apply hd.congr_of_eventuallyEq
    filter_upwards [hue] with v hv
    exact congrArg f hv.1
  have hqt := hlocal.self_of_nhds
  have hsecond := (((hF (q t) hqt.2.1).fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t hqt.2.2.1
  have hfield := hsecond.clm_apply hqt.2.2.2
  have hcancel := D.hessian_in_chart p hqt.2.1 (hf _) (w t) (w t)
  rw [hzero] at hcancel
  have hvalue : fderiv ℝ (fderiv ℝ F) (q t) (w t) (w t) -
      fderiv ℝ F (q t)
        (coordinateChristoffel (g.pullbackCoefficients c.symm) (q t) (w t) (w t)) = 0 := by
    simpa only [CoordinateExponential.christoffelBilinear_apply] using hcancel.symm
  have hfield0 : HasDerivAt (fun u => fderiv ℝ F (q u) (w u)) 0 t := by
    rw [← hvalue]
    simpa +instances only [Function.comp_def, map_neg, ← sub_eq_add_neg] using hfield
  exact hfield0.congr_of_eventuallyEq (hfirst.mono fun _ hu => hu.deriv)

theorem deriv_comp_geodesic_eq_initial
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hzero : HasZeroHessian D f)
    (hγ : g.IsGeodesicOn γ univ) (t : ℝ) :
    deriv (f ∘ γ) t = deriv (f ∘ γ) 0 := by
  exact isOpen_univ.is_const_of_deriv_eq_zero
    (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
    (fun u _ => (hasDerivAt_deriv_comp_geodesic_eq_zero hf hzero hγ
      (mem_univ u)).differentiableAt.differentiableWithinAt)
    (fun u _ => (hasDerivAt_deriv_comp_geodesic_eq_zero hf hzero hγ
      (mem_univ u)).deriv) (mem_univ t) (mem_univ 0)

theorem comp_geodesic_eq_affine [T3Space M]
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hzero : HasZeroHessian D f)
    (hγ : g.IsGeodesicOn γ univ) (t : ℝ) :
    f (γ t) = f (γ 0) + t * deriv (f ∘ γ) 0 := by
  have hφ : Differentiable ℝ (f ∘ γ) :=
    (contMDiff_iff_contDiff.mp (hf.comp (contMDiff_global_geodesic hγ))).differentiable
      (by simp)
  have hψ (u : ℝ) : HasDerivAt (fun s => f (γ 0) + s * deriv (f ∘ γ) 0)
      (deriv (f ∘ γ) 0) u := by
    simpa +instances only [id_eq, one_mul] using
      ((hasDerivAt_id u).mul_const (deriv (f ∘ γ) 0)).const_add (f (γ 0))
  have heq := isOpen_univ.eqOn_of_deriv_eq
    (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected hφ.differentiableOn
    (fun u _ => (hψ u).differentiableAt.differentiableWithinAt)
    (fun u _ => (deriv_comp_geodesic_eq_initial hf hzero hγ u).trans (hψ u).deriv.symm)
    (mem_univ (0 : ℝ)) (by simp)
  exact heq (mem_univ t)

theorem geodesic_velocity_eq_gradient [T3Space M]
    {D : LeviCivitaData g} {f : M → ℝ} {γ : ℝ → M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hunit : HasUnitGradient D f)
    (hzero : HasZeroHessian D f) (hγ : g.IsGeodesicOn γ univ)
    (hinit : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 = D.gradient f (γ 0)) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 = D.gradient f (γ t) := by
  have hγs := contMDiff_global_geodesic hγ
  have hd (u : ℝ) : deriv (f ∘ γ) u =
      mvfderiv (𝓡 n) f (γ u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1) := by
    have heq := congrArg (fun L => L 1) (mfderiv_comp u
      ((hf (γ u)).mdifferentiableAt (by simp)) ((hγs u).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    exact heq
  have hdf0 : deriv (f ∘ γ) 0 = 1 := by
    rw [hd, hinit, ← D.inner_gradient]
    exact hunit _
  have hpair : g.inner (γ t) (D.gradient f (γ t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1 := by
    rw [D.inner_gradient, ← hd, deriv_comp_geodesic_eq_initial hf hzero hγ t, hdf0]
  have hspeed : g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1 := by
    have heq := isOpen_univ.is_const_of_deriv_eq_zero
      (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
      (fun u _ => (hγ.hasDerivAt_tangentNorm_zero (mem_univ u)).differentiableAt
        |>.differentiableWithinAt)
      (fun u _ => (hγ.hasDerivAt_tangentNorm_zero (mem_univ u)).deriv)
      (mem_univ t) (mem_univ 0)
    rw [heq, hinit, tangentNorm, hunit, Real.sqrt_one]
  have hnorm : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1 := Real.sqrt_eq_one.mp hspeed
  by_contra hne
  have hpos := g.pos (γ t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 - D.gradient f (γ t)) (sub_ne_zero.mpr hne)
  have hsymm := g.symm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) (D.gradient f (γ t))
  simp only [map_sub, sub_apply] at hpos
  rw [hnorm, hsymm, hpair, hunit] at hpos
  norm_num at hpos

end PoincareConjecture.RiemannianMetric
