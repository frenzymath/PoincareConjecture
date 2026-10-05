import PoincareLib.Topology.Manifold.EmbeddedSphere.Homology.NullHomotopy
import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralRelativeChains
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Relative classes bounding classes on the embedded sphere

The sphere range inclusion induces zero in positive-degree homology. Exactness
of the pair sequence therefore supplies relative classes with any prescribed
positive-degree boundary on the sphere. This follows Hatcher, Section 2.1,
pp. 113-115, and is the relative-class step in M53 derivation 02 for the
separation repair used in Morgan--Tian Proposition 15.12, printed p. 365.
-/

set_option autoImplicit false

open CategoryTheory
open scoped Manifold ContDiff

universe u

namespace PoincareMT.Topology.EmbeddedSphere

open Poincare.Topology

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Every positive-degree integral homology class on the sphere range is a
relative boundary. Source: Hatcher's exact sequence of a pair, pp. 113-115,
and M53 derivation 02 for Morgan--Tian Proposition 15.12, printed p. 365. -/
theorem sphereRelativeBoundary_surjective
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) (n : Nat) (hn : n ≠ 0) :
    Function.Surjective (integralRelativeBoundary (Set.range S.sphere) n) := by
  intro c
  have hexact := (integralPairSequence_shortExact (Set.range S.sphere)).homology_exact₁
    (n + 1) n rfl
  apply (ShortComplex.moduleCat_exact_iff _).mp hexact c
  change (HomologicalComplex.homologyMap
    (integralSubspaceChains (Set.range S.sphere)) n) c = 0
  have hzero : HomologicalComplex.homologyMap
      (integralSubspaceChains (Set.range S.sphere)) n = 0 :=
    sphereRangeInclusion_homologyMap_eq_zero
      (C := ModuleCat.{u} Int) integralCoefficient S n hn
  rw [hzero]
  rfl

end PoincareMT.Topology.EmbeddedSphere
