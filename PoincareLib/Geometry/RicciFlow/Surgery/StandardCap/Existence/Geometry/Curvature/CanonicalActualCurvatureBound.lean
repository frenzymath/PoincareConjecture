import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CanonicalCurvatureNorms
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CurvatureRepresentative

/-!
# Uniform fixed-model norms of actual canonical curvature

The selected trilinear representative has the exact actual raw entries.
The existing elliptic-jet background bound therefore controls its model
operator norm before choosing the domain or geometry. This is
Morgan-Tian Section 12.5, pp. 309-319 and
core-overlap-and-energy-majorants.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The curvature fiber contains three nested Hom spaces.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

open DifferenceEnergy

/-- Elliptic metric three-jets uniformly control the selected actual
curvature representative in the ambient model norm
(Section 12.5, pp. 309-319). -/
theorem exists_canonicalDomain_actualCurvature_norm_bound
    (n : ℕ) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
      letI := hNE
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j
          (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm) x‖ ≤ M) →
        (∀ v, a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x v v) →
        norm (E := FS n) (curvatureTrilinearMap D ((extChartAt (𝓡 n) p).symm x)) ≤ C := by
  obtain ⟨C, hC, hb⟩ := canonicalDomain_background_operatorNorm_bound n ha M
  refine ⟨C, hC, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx hj he
  let R : FS n := curvatureTrilinearMap D ((extChartAt (𝓡 n) p).symm x)
  have hraw : raw R = canonicalDomain_curvatureArray U hU g D p x := by
    funext l j k m
    exact congrArg (EuclideanSpace.proj l)
      (curvatureTrilinearMap_apply D ((extChartAt (𝓡 n) p).symm x)
        (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) (EuclideanSpace.single m 1))
  exact (hb U hU hNE g D p x hx hj he R hraw).2

end PoincareMT.M34
