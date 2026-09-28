import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.ManifoldJacobiPairing
import PoincareConjecture.Statements.M64Comparison















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open ConnectionAlongCurve ConnectionVariation

set_option maxHeartbeats 1000000 in




theorem m64Intrinsic_manifold_jacobi_half_inner_one_lower_bound
    (N : IntrinsicAnnulus) {q : ℝ → AnnulusCoordinates} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 2) (q t)} {K c : ℝ}
    (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ q I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hsub : Icc 0 1 ⊆ I)
    (hjac : ∀ t ∈ I,
      manifoldCovDerivAlong N.metric q
          (manifoldCovDerivAlong N.metric q J 1) 1 t =
        -N.connection.curvature (q t) (J t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) q t 1))
    (hK : ∀ t ∈ Icc 0 1,
      N.connection.curvatureTensorNorm (q t) ≤ K)
    (hc : ∀ t ∈ Icc 0 1,
      N.metric.tangentNorm (q t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) q t 1) = c)
    (hcr : c ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4)
    (hJ0 : J 0 = 0) :
    N.metric.tangentNorm (q 0)
        (manifoldCovDerivAlong N.metric q J 1 0) ^ 2 / 2 ≤
      N.metric.inner (q 1)
        (manifoldCovDerivAlong N.metric q J 1 1) (J 1) := by
  exact ManifoldJacobi.manifold_jacobi_half_inner_one_lower_bound
    N.connection hI hq hJ hsub hjac hK hc hcr hJ0

end PoincareConjecture
