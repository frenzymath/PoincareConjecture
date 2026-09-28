import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartDifferential
import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartPrefix
import PoincareConjecture.Proofs.M14.Sec6_5_SquareScalarField

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

theorem positiveStart_time_derivative_square
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hp : M14IsMinimizing p)
    (R : M14SquareRootPath G p)
    (U : Set G.Point) (hU : IsOpen U) (hy : y ∈ U)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T a x) U) :
    M14BackwardTimeDerivative G (M14ReducedLengthAt G T a x) (R.curve (Real.sqrt b)) =
      horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) / 2 -
        G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
          (R.horizontal_velocity (Real.sqrt b)) (R.horizontal_velocity (Real.sqrt b)) /
            (8 * (Real.sqrt b) ^ 2) -
        M14BackwardLAction G p / (4 * (Real.sqrt b) ^ 3) := by
  have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) _ hs
  have hpoint : R.curve (Real.sqrt b) = y := by
    rw [R.agrees _ hs, Real.sq_sqrt hb.le, p.curve_end]
  have hRU : R.curve (Real.sqrt b) ∈ U := by rwa [hpoint]
  have hchain := squareRoot_scalarField_hasDerivWithinAt R hs
    (((hf _ hRU).contMDiffAt (hU.mem_nhds hRU)).mdifferentiableAt (by simp))
  rw [positiveStart_horizontal_differential hCoordinates hM12 hp U hU hy hf] at hchain
  have hnorm := positiveStart_reducedLengthAt_square_hasDerivWithinAt hM12 hp R
  have heq := (hchain.derivWithin hC).symm.trans (hnorm.derivWithin hC)
  dsimp only [squareRootLIntegrand] at heq
  field_simp [(Real.sqrt_pos.mpr hb).ne'] at heq ⊢
  nlinarith [heq]

end PoincareConjecture.M14
