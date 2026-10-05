import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Exponential.ExponentialFamily
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Geometry.GeometryAssembly
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.RegularLocus.RegularLocusAssembly
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.RegularLocus.RegularLaplacian
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Barrier.ZeroResidualBarrier
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Barrier.LocalBarrierBounds
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.RegularLocus.RegularSharpEquality

/-!
# Reduced-length differential inequality proof assembly

The theorem packages the regular-locus computation and the upper-barrier
extension for the fixed-carrier bounded-curvature flow. Its hypotheses retain
the curvature theory and L-geodesic theory as explicit predecessor inputs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- M09: for a connected ordinary Ricci flow complete with one full-curvature
bound on [T-taumax,T], M04 and M08 give coherent L-exponential geometry with
initial square-root velocity 2Z and its actual Jacobi differential. The
canonical minimizing regular domain is a smooth exponential chart, nested
toward zero and eventually containing each bounded initial tangent ball.
For 0 < tau < taumax, reduced length has an open dense regular locus and
satisfies its six differential identities and inequalities. Sharp Laplacian
equality gives Ric + Hess(l) = g/(2*tau) on the same regular branch. At every
point there are the stated upper barriers, including locally uniform time,
gradient and spatial Hessian bounds. Measure and reduced-volume conclusions
belong to M10.

Sources: Morgan-Tian Definition 6.17 and Lemmas 6.18-6.23, pp. 113-116;
Propositions 6.28-6.31, pp. 117-119; Propositions 6.37/6.43, pp. 123-129;
Theorem 6.50 and Corollary 6.51, pp. 131-132; Proposition 6.78 and
Corollary 6.79, pp. 143-145; Proposition 7.5, pp. 151-152;
Proposition 7.8, pp. 152-154; Lemma 7.15, pp. 157-158.
Use the corrected prefix coefficient and additive small-time action error in
`reviews/errata/2026-09-13-reduced-length-source.md`, together with M08's
connection-time transport and M04's corrected Ricci contraction.
`reviews/contracts/M09-round1.md` gives the complete source derivation. -/
theorem reducedLengthDifferentialInequalities
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hL : LGeodesicTheory F T τmax) :
    Nonempty (ReducedLengthDifferentialTheory F T τmax) := by
  classical
  let A (p : M) : LExponentialFamily F T τmax p :=
    Classical.choice (ReducedLength.nonempty_lExponentialFamily F hM04 T τmax
      hτmax hwindow hcurvature p)
  let G (p : M) : LExponentialGeometry F T τmax p :=
    Classical.choice (ReducedLength.lExponentialFamily_exists_geometry F hM04 T τmax
      hτmax hwindow hcurvature hL p (A p))
  refine ⟨{
    regular_locus := fun p τ hτ hmax ↦
      ReducedLength.lExponentialGeometry_regular_locus F hM04 T τmax hτmax hwindow
        hcurvature hL p (G p) τ hτ hmax
    regular_point_formulas := fun p _ _ r ↦
      ReducedLength.regular_six_formulas hM04 hL hτmax hwindow (A p) r
    upper_barrier_extension := fun p q τ hτ hmax ε hε ↦
      ReducedLength.exists_upperBarrier_with_residual_le hM04 hL hτmax hwindow
        (A p) q τ hτ hmax ε hε
    exponential_geometry := fun p ↦ ⟨G p⟩
    local_upper_barrier_bounds := fun p z hz ↦
      ReducedLength.lExponentialFamily_local_upper_barrier_bounds F hM04 T τmax
        hτmax hwindow hcurvature hL p (A p) z hz
    regular_point_equality := ?_
  }⟩
  intro p H z hz
  exact ReducedLength.regular_sharp_laplacian_tensor_eq hM04 hL hτmax hwindow
    H.toLExponentialFamily (H.regular_point z hz)

end PoincareMT
