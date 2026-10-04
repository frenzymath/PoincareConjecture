import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Level
import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Flow

/-!
# Curvature of the parallel-gradient splitting factor

`parallelGradient_factor_curvature` proves total geodesicity, curvature
restriction, and all three metric trace identities for `regularLevelMetric`
and its constructed Levi-Civita connection.

`exists_parallelGradient_productIsometry_curvature` transports the scalar and
full-norm identities to every ambient point and proves inheritance of operator
nonnegativity, uniform full-curvature bounds, and positive scalar curvature.
-/
