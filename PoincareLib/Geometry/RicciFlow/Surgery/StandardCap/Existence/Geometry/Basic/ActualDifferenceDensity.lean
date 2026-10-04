import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CurvatureRepresentative
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.DifferenceFluxAlgebra

/-!
# The actual metric, connection and curvature difference density

Fixed finite coordinates are applied to the actual three tensor
differences, using the continuous trilinear representative of retained
curvature. The sum of their coordinate squares is nonnegative at every
point. On canonical open domains these are precisely the fields in the
local energy estimates of Morgan-Tian Section 12.5, pp. 309-319.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The actual curvature fiber has three nested Hom spaces.
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

universe u

variable {n dH dA dS : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
  {g g' : RiemannianMetric n M} (D : LeviCivitaData g) (D' : LeviCivitaData g')

/-- The coordinate sum of squares of the actual metric, connection and
raised-curvature differences (Section 12.5, pp. 309-319). -/
noncomputable def actualDifferenceEnergyDensity (x : M) : ℝ :=
  let H : FH n := g.inner x - g'.inner x
  let A : FA n := CovariantDerivative.difference D.connection D'.connection x
  let S : FS n := curvatureTrilinearMap D x - curvatureTrilinearMap D' x
  (∑ i, qH H i ^ 2) + (∑ i, qA A i ^ 2) + (∑ i, qS S i ^ 2)

/-- The actual difference density is pointwise nonnegative, including in
zero dimension (Section 12.5, pp. 309-319). -/
theorem actualDifferenceEnergyDensity_nonneg (x : M) :
    0 ≤ actualDifferenceEnergyDensity qH qA qS D D' x := by
  dsimp only [actualDifferenceEnergyDensity]
  positivity

end PoincareMT.M34
