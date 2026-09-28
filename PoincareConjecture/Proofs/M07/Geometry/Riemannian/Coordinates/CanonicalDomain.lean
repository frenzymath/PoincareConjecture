import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Geometry.Manifold.ContMDiff.Atlas









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_canonicalChart
    {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U] :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (p x : U),
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (x : EuclideanSpace ℝ (Fin n)) =
        g.inner x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g p x
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  have hc : extChartAt (𝓡 n) p = extChartAt (𝓡 n) x := rfl
  rw [hc]
  ext v w
  change g.inner ((extChartAt (𝓡 n) x).symm x)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm x v)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm x w) = g.inner x v w
  have hx : (extChartAt (𝓡 n) x).symm (x : EuclideanSpace ℝ (Fin n)) = x :=
    (extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)
  change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
    (x : EuclideanSpace ℝ (Fin n)) = ContinuousLinearMap.id ℝ _ at hd
  rw [hd, hx]
  rfl

end PoincareConjecture.RiemannianMetric
