import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Main
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.ShortLoops
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Core
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Basic
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Theory

/-!
# M60 filling and sphere-area proof entry

The analytic and filling core is assembled from its proved suppliers and
M04's applied tensor calculus and scalar regularity. M58 supplies the
short-loop disk estimate and the checked disk-to-infimum comparison.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- M60: given M04 and M58, every C1 sphere map into a smooth Riemannian
n-manifold has integrable area and half-energy densities, with nonnegative
area at most energy and equality for weakly conformal maps. On a compact
three-manifold, each null C1 loop has finite admissible fillings and area
near-minimizers; the infimum is nonnegative, invariant under boundary
reparameterization and continuous on null loops in the C1 topology.

A compact Riemannian n-manifold with nontrivial pi2 at a chosen point has
a positive least area over all non-null C1 sphere maps, attained by a
nonconstant smooth branched minimal sphere. For any fixed C1 sphere map
along a compact Ricci-flow slab [a,b], a<b, with actual Ricci norm bounded
by D>=0, area has the correct negative Ricci-trace derivative within the
slab, absolute derivative at most 4*D*A, a nonincreasing integrating factor,
and exponential comparison in both time orders. Rank-deficient maps are
included. In dimension three, if that map is branched minimal at an included
time, its derivative is at most -4*pi-(rho/2)*A for every scalar lower bound
rho, including the actual attained scalar minimum.

For every eta>0 on a compact three-manifold, M58 supplies the same
0<zeta<eta/2 and disk of area<eta for each C1 loop of length<zeta; the checked
infimum comparison gives fillingArea<eta without any pi2 or pi3 assumption.
All target manifolds are Hausdorff, second countable and boundaryless.

Sources: Morgan--Tian Lemma 18.10, Claims 18.12-18.13, Definition 18.17 and
corrected Corollary 18.28, pp. 424-428, 430 and 434; Hamilton (1999)
Section 11, pp. 716-719, specialized to fixed closed spheres and unnormalized
flow; Sacks--Uhlenbeck (1981), Theorem 1.6, Proposition 2.4, Theorems 2.1,
3.3, 3.6, 4.4, 4.6, 4.7 and Lemma 5.4, pp. 4-8, 12-18 and 21-22.
Retain the corrected variation factor, annular homotopy argument and
normalization in `reviews/errata/2026-09-14-sphere-area.md`. The complete
derivation and original-source archive status are recorded in
`reviews/contracts/M60-round1.md` and
`references/m60-source-verification-2026-09-14.md`. -/
theorem m60AreaAndFilling
    (P04 : RicciFlowCurvatureTheory.{u})
    (P58 : RepairedShortLoopTrivialityTheory.{u}) :
    M60AreaTheory.{u} := by
  have core :
      (∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus) →
      (∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (J : Set ℝ) (F : RicciFlow n M J),
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
          (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)) →
      M60AreaCore.{u} := by
    intro tensor scalar
    exact m60AreaCore_of_leastSphere tensor scalar m60LeastSphere_of_suProducers
  exact { toM60AreaCore := core P04.tensor_calculus P04.scalar_regular
          short_loop := m60ShortLoopAreaClaim_from_M58 P58 }

/-- Supply the exact earlier milestones once for downstream consumers. -/
theorem m60AreaAndFilling_from_predecessors : M60AreaTheory.{u} :=
  m60AreaAndFilling ricciFlowCurvatureTheory repairedShortLoopTriviality

end PoincareMT
