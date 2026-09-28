import PoincareConjecture.Proofs.M53.Prop15_12_NullHomology
import PoincareConjecture.Proofs.M02.Topology.IntegralRelativeChains
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option autoImplicit false

open CategoryTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M53

open PoincareConjecture.Proofs.M02.Topology

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

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

end PoincareConjecture.Proofs.M53
