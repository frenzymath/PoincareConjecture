import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.IntrinsicGeometry.IntrinsicOpenMetric

/-!
# The guarded partial diffeomorphism of actual open inclusion

Keep the inherited manifold structure and the original total inverse.
This is used twice in the raw source map for Morgan--Tian Proposition
10.7, p. 253; M28 derivation 102.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- The actual inclusion has full subtype source and the literal open set
as target. Its inverse is smooth only on that target.
Source: Proposition 10.7, p. 253; M28 derivation 102. -/
noncomputable def openSubtypePartialDiffeomorph (U : TopologicalSpace.Opens M)
    (hne : Nonempty U) : PartialDiffeomorph (𝓡 3) (𝓡 3) U M ∞ :=
  let e := U.openPartialHomeomorphSubtypeCoe hne
  { toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := (contMDiff_subtype_val (I := 𝓡 3) (U := U)).contMDiffOn
    contMDiffOn_invFun := by
      change ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target
      rw [show e.target = (U : Set M) from U.openPartialHomeomorphSubtypeCoe_target hne]
      exact openSubtypeInverse_contMDiffOn U hne }

/-- The inclusion is defined smoothly on its entire actual subtype.
Source: the raw-stage composition in M28 derivation 102. -/
@[simp] theorem openSubtypePartialDiffeomorph_source
    (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
    (openSubtypePartialDiffeomorph U hne).source = univ :=
  U.openPartialHomeomorphSubtypeCoe_source hne

/-- The inverse domain is precisely the original open subset.
Source: the raw-stage composition in M28 derivation 102. -/
@[simp] theorem openSubtypePartialDiffeomorph_target
    (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
    (openSubtypePartialDiffeomorph U hne).target = (U : Set M) :=
  U.openPartialHomeomorphSubtypeCoe_target hne

/-- Forward evaluation is the unchanged subtype inclusion.
Source: the exact metric-map identity in M28 derivation 102. -/
@[simp] theorem openSubtypePartialDiffeomorph_apply
    (U : TopologicalSpace.Opens M) (hne : Nonempty U) (x : U) :
    openSubtypePartialDiffeomorph U hne x = x.val := rfl

end PoincareMT.M28
