import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem hasDerivAt_density {x : EuclideanSpace ℝ (Fin n)} {τ : ℝ}
    (hx : x ∈ e.source) (hτ : -τ ∈ interior J) :
    HasDerivAt (fun σ => density F e (x, σ))
      ((F.connection (-τ)).scalarCurvature (e x) * density F e (x, τ)) τ := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have h := F.hasDerivAt_pullbackVolumeDensity hτ
    (F.connection (-τ)).intrinsicCurvatureTensorCalculus e x
    (hD.mfderiv_injective hx)
  have hn := h.comp τ (hasDerivAt_id τ).neg
  simpa only [Function.comp_def, density, id_eq, neg_mul, mul_neg, neg_neg,
    mul_one] using hn

theorem timeDeriv_density {z : Spacetime n} (hz : z ∈ domain J e) :
    Canonical.timeDeriv (density F e) z =
      (F.connection (-z.2)).scalarCurvature (e z.1) * density F e z := by
  have h := ((contDiffOn_density F e he hei).contDiffAt
    ((isOpen_domain e).mem_nhds hz)).differentiableAt (by simp)
  have hd := h.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  exact hd.unique (hasDerivAt_density F e he hei hz.1 hz.2)

end PoincareConjecture.RicciFlow.BackwardCoordinates
