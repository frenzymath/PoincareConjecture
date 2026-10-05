import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.CenteredQuadratic
import PoincareLib.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Metric.Hessian.LaplacianLinearity

/-!
# Local linearity for actual scalar support jets

Morgan-Tian, Section 12.5, p. 304: distance upper supports only have to be
smooth near their contact point. The growing-barrier maximum principle
therefore uses linearity of the retained Hessian and Laplacian under
pointwise smoothness hypotheses, without a global extension of a support.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.Uniqueness

/-- Section 12.5, p. 304: addition of actual scalar Hessian jets only
requires smoothness at the contact point. -/
theorem hessian_add_at
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    {f h : StandardCapSpace → ℝ} {x : StandardCapSpace}
    (hf : ContDiffAt ℝ ∞ f x) (hh : ContDiffAt ℝ ∞ h x)
    (v w : StandardCapSpace) :
    D.hessian (fun y => f y + h y) x v w =
      D.hessian f x v w + D.hessian h x v w := by
  have hfirst : fderiv ℝ (fun y => f y + h y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y + fderiv ℝ h y) := by
    filter_upwards [(hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp),
      (hh.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with y hyf hyh
    exact (hyf.differentiableAt (by simp)).hasFDerivAt.add
      (hyh.differentiableAt (by simp)).hasFDerivAt |>.fderiv
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.add
    ((hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (fun y => fderiv ℝ f y + fderiv ℝ h y) _ x at hd
  rw [D.hessian_eq_fderiv_sub_christoffel (hf.add hh),
    D.hessian_eq_fderiv_sub_christoffel hf, D.hessian_eq_fderiv_sub_christoffel hh,
    hfirst.fderiv_eq, hd.fderiv, hfirst.eq_of_nhds]
  simp only [add_apply]
  ring

/-- Section 12.5, p. 304: the actual Laplacian is additive on local
smooth upper supports at their contact point. -/
theorem laplacian_add_at
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    {f h : StandardCapSpace → ℝ} {x : StandardCapSpace}
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ f x)
    (hh : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ h x) :
    D.laplacian (fun y => f y + h y) x = D.laplacian f x + D.laplacian h x := by
  simp only [LeviCivitaData.laplacian,
    hessian_add_at D (contMDiffAt_iff_contDiffAt.mp hf) (contMDiffAt_iff_contDiffAt.mp hh),
    Finset.sum_add_distrib]

/-- Section 12.5, p. 304: adding the constant one to a local distance
support does not change its actual scalar Laplacian. -/
theorem laplacian_const_add_at
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    {f : StandardCapSpace → ℝ} {x : StandardCapSpace}
    (hf : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ f x) (c : ℝ) :
    D.laplacian (fun y => c + f y) x = D.laplacian f x := by
  rw [laplacian_add_at D contMDiffAt_const hf, M10.laplacian_const_scalar, zero_add]

end PoincareMT.M35.Uniqueness
