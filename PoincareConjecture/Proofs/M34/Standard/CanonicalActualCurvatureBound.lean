import PoincareConjecture.Proofs.M34.Standard.CanonicalCurvatureNorms
import PoincareConjecture.Proofs.M34.Standard.CurvatureRepresentative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy

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

end PoincareConjecture.M34
