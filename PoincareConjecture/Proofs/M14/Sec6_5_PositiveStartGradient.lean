import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartDifferential
import PoincareConjecture.Proofs.M14.Sec6_5_GradientNorm









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

private theorem differential_transport {q r : G.Point} (h : q = r)
    (f : G.Point → ℝ) (A : G.Horizontal q) (c : ℝ)
    (hd : ∀ V : G.Horizontal q, mvfderiv (spacetimeModel n) f q V.val =
      G.spacetime.horizontalMetric.inner q A V / c) :
    ∀ V : G.Horizontal r, mvfderiv (spacetimeModel n) f r V.val =
      G.spacetime.horizontalMetric.inner r (h ▸ A) V / c := by
  cases h
  exact hd

private theorem inner_transport {q r : G.Point} (h : q = r) (A : G.Horizontal q) :
    G.spacetime.horizontalMetric.inner r (h ▸ A) (h ▸ A) =
      G.spacetime.horizontalMetric.inner q A A := by
  cases h
  rfl




theorem positiveStart_gradient_norm_square
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hp : M14IsMinimizing p)
    (R : M14SquareRootPath G p)
    (U : Set G.Point) (hU : IsOpen U) (hy : y ∈ U)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T a x) U)
    (B : Module.Basis (Fin n) ℝ (G.Horizontal y))
    (hB : ∀ i j, G.spacetime.horizontalMetric.inner y (B i) (B j) =
      if i = j then 1 else 0) :
    M14ReducedLengthGradientNormSq (T := T) (τ₁ := a) G x y B =
      G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
        (R.horizontal_velocity (Real.sqrt b)) (R.horizontal_velocity (Real.sqrt b)) /
          (4 * (Real.sqrt b) ^ 2) := by
  have hpoint : R.curve (Real.sqrt b) = y := by
    rw [R.agrees _ ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩,
      Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le), p.curve_end]
  have hd := differential_transport hpoint (M14ReducedLengthAt G T a x)
    (R.horizontal_velocity (Real.sqrt b)) (2 * Real.sqrt b)
      (positiveStart_horizontal_differential hCoordinates hM12 hp U hU hy hf)
  rw [reducedLengthGradientNormSq_eq_of_differential x y B hB
    (hpoint ▸ R.horizontal_velocity (Real.sqrt b)) (2 * Real.sqrt b) hd,
    inner_transport hpoint]
  congr 1
  ring

end PoincareConjecture.M14
