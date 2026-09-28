import PoincareConjecture.Proofs.M34.Standard.CurvatureRepresentative
import PoincareConjecture.Proofs.M34.Standard.DifferenceFluxAlgebra











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

universe u

variable {n dH dA dS : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
  {g g' : RiemannianMetric n M} (D : LeviCivitaData g) (D' : LeviCivitaData g')



noncomputable def actualDifferenceEnergyDensity (x : M) : ℝ :=
  let H : FH n := g.inner x - g'.inner x
  let A : FA n := CovariantDerivative.difference D.connection D'.connection x
  let S : FS n := curvatureTrilinearMap D x - curvatureTrilinearMap D' x
  (∑ i, qH H i ^ 2) + (∑ i, qA A i ^ 2) + (∑ i, qS S i ^ 2)



theorem actualDifferenceEnergyDensity_nonneg (x : M) :
    0 ≤ actualDifferenceEnergyDensity qH qA qS D D' x := by
  dsimp only [actualDifferenceEnergyDensity]
  positivity

end PoincareConjecture.M34
