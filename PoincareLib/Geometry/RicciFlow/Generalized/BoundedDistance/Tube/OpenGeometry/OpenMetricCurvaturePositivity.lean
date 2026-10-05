import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.IntrinsicGeometry.IntrinsicOpenMetric
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Geometry.OperatorRicci

/-!
# Curvature positivity on the literal intrinsic open metric

The actual inclusion is a local isometry of inner products. Curvature
positivity therefore transfers to every compatible connection on the
restricted metric, without identifying ambient and intrinsic distances.
Source: Morgan--Tian Claim 10.11, p. 255; M28 derivation 161b.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M28

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The inclusion preserves the exact curvature-operator predicate for
any compatible connections on the ambient and literal restricted metric.
Source: MT Claim 10.11, p. 255; derivation 161b. -/
theorem intrinsicOpenMetric_nonnegativeCurvatureOperator_iff
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (D : LeviCivitaData g) (DU : LeviCivitaData (intrinsicOpenMetric g U))
    (x : U) :
    DU.NonnegativeCurvatureOperator x ↔ D.NonnegativeCurvatureOperator (x : M) := by
  exact DU.nonnegativeCurvatureOperator_iff_of_local_isometry D
    (f := (Subtype.val : U → M)) isOpen_univ
    (contMDiff_subtype_val (I := 𝓡 3) (U := U)).contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

/-- Ambient operator nonnegativity on an open region gives sectional
nonnegativity for every compatible connection on its literal intrinsic
metric. Source: MT Claim 10.11, p. 255; derivation 161b. -/
theorem intrinsicOpenMetric_nonnegativeSectionalCurvature_of_operator
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (D : LeviCivitaData g) (DU : LeviCivitaData (intrinsicOpenMetric g U))
    (hD : ∀ x : U, D.NonnegativeCurvatureOperator (x : M)) :
    DU.NonnegativeSectionalCurvature := by
  intro x v w
  exact DU.sectional_nonneg_of_nonnegative_operator_m28 x
    ((intrinsicOpenMetric_nonnegativeCurvatureOperator_iff g U D DU x).mpr (hD x)) v w

end PoincareMT.M28
