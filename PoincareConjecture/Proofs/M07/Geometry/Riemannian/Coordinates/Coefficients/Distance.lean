import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ChartSegment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem toReal_edist_le_of_pullback_upper (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hconv : Convex ℝ U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {b : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ x ∈ U, ∀ v : EuclideanSpace ℝ (Fin n),
      g.pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (hy : y ∈ U) :
    (g.edist (e x) (e y)).toReal ≤ Real.sqrt b * dist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let K : ℝ≥0 := ⟨Real.sqrt b, Real.sqrt_nonneg _⟩
  have hnorm (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ U) :
      ‖mfderiv (𝓡 n) (𝓡 n) e z‖ ≤ Real.sqrt b := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hh := Real.sqrt_le_sqrt (hupper z hz v)
    rw [norm_eq_sqrt_real_inner]
    simpa only [pullbackCoefficients, ContinuousLinearMap.bilinearComp_apply,
      Real.sqrt_mul hb, Real.sqrt_sq (norm_nonneg v)] using! hh
  have hdist := Poincare.riemannianEDist_le_mul_edist_of_convex hconv
    (fun z hz ↦ (he.contMDiffAt (hU.mem_nhds hz)).of_le (by simp))
    (K := K) (fun z hz ↦ by
      rw [enorm_eq_nnnorm]
      exact_mod_cast hnorm z hz) hx hy
  have hfinite : (K : ℝ≥0∞) * EDist.edist x y ≠ ⊤ := by finiteness
  have hreal := ENNReal.toReal_mono hfinite hdist
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] at hreal
  convert! hreal using 1

end PoincareConjecture.RiemannianMetric
