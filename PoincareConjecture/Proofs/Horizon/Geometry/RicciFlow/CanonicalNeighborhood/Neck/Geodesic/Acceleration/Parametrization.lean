import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Coordinates


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem axial_hessian_of_smooth_parametrization
    (D : LeviCivitaData g)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M)
    (hB : ContMDiffOn (𝓡 3) (𝓡 3) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ B.symm B.target)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ B.source)
    {f : M → ℝ} {ell : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ}
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ f (B p))
    (hcomp : (fun x : EuclideanSpace ℝ (Fin 3) => f (B x)) =ᶠ[𝓝 p]
      (fun x : EuclideanSpace ℝ (Fin 3) => ell x))
    (v w : EuclideanSpace ℝ (Fin 3)) :
    D.hessian f (B p) (mfderiv (𝓡 3) (𝓡 3) B p v)
        (mfderiv (𝓡 3) (𝓡 3) B p w) =
      -ell (CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients B) p v w) := by
  rw [D.hessian_in_smooth_local_parametrization B hB hBi hp hf v w]
  have hcomp' : fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => f (B x)) p = ell := by
    rw [hcomp.fderiv_eq]
    exact ell.hasFDerivAt.fderiv
  have hcomp'' : fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => f (B x))) p =
      0 := by
    have hdd :
        fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => f (B x))) p =
          fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => ell x)) p :=
      hcomp.fderiv.fderiv_eq
    rw [hdd]
    have hlin : fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => ell x)) p = 0 := by
      change fderiv ℝ (fderiv ℝ ell) p = 0
      have hfun : (fderiv ℝ (ell : EuclideanSpace ℝ (Fin 3) → ℝ)) =
          (fun _ : EuclideanSpace ℝ (Fin 3) => ell) := by
        funext x
        exact ContinuousLinearMap.fderiv ell
      rw [hfun]
      exact (hasFDerivAt_const (𝕜 := ℝ) (c := ell) p).fderiv
    exact hlin
  change (fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => f (B x))) p) v w -
      (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => f (B x)) p)
        (CoordinateExponential.christoffelBilinear (g.pullbackCoefficients B) p v w) = _
  rw [hcomp', hcomp'']
  simp only [fderiv_const, zero_apply, zero_sub]

end PoincareConjecture.EpsilonNeck
