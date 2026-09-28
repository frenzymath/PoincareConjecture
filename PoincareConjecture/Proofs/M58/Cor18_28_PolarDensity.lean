import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import PoincareConjecture.Proofs.M58.Mathlib.TwoVectorArea










set_option autoImplicit false

open Set Real Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem mul_parametrizedAreaDensity_le_polar (g : RiemannianMetric 3 M)
    (F : LoopPlane → M) (z : LoopPlane) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    r * parametrizedAreaDensity g F z ≤
      g.tangentNorm (F z) (mfderiv (𝓡 2) (𝓡 3) F z (angularPoint t)) *
      g.tangentNorm (F z) (mfderiv (𝓡 2) (𝓡 3) F z (r • angularVector t)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let D := mfderiv (𝓡 2) (𝓡 3) F z
  let u := D (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let v := D (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have harea : parametrizedAreaDensity g F z = twoVectorArea u v := by
    unfold parametrizedAreaDensity twoVectorArea
    dsimp only
    erw [Matrix.det_fin_two]
    change sqrt (max 0 (inner ℝ u u * inner ℝ v v - inner ℝ u v * inner ℝ v u)) = _
    rw [real_inner_comm v u, pow_two]
  have hrep (w : LoopPlane) : D w = w 0 • u + w 1 • v := by
    have hw : w = w 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        w 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
      simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr w).symm
    calc
      D w = D (w 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
          w 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1) := congrArg D hw
      _ = _ := by erw [map_add, map_smul, map_smul]
  have hframe : twoVectorArea (D (angularPoint t)) (D (r • angularVector t)) =
      r * parametrizedAreaDensity g F z := by
    rw [hrep, hrep]
    change twoVectorArea (cos t • u + sin t • v) ((r * -sin t) • u + (r * cos t) • v) = _
    rw [twoVectorArea_change]
    have hdet : cos t * (r * cos t) - sin t * (r * -sin t) = r := by
      calc
        _ = r * (cos t ^ 2 + sin t ^ 2) := by ring
        _ = r := by rw [cos_sq_add_sin_sq, mul_one]
    rw [hdet, abs_of_nonneg hr, ← harea]
  exact hframe ▸ twoVectorArea_le (D (angularPoint t)) (D (r • angularVector t))

end PoincareConjecture.Proofs.M58
