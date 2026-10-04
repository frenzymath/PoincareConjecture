import PoincareLib.Geometry.Spacetime.Horizontal.Basic

/-!
# Curvature evaluation on an identified time slice

A time equality identifies the dependent slice point, its selected charts,
the retained connection and the inverse tangent maps simultaneously. These
lemmas evaluate horizontal curvature on any specified equal time slice.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ s : ℝ, SpacetimeSliceGeometry F s}

/-- Evaluate horizontal Riemann curvature on an identified actual time slice. -/
theorem horizontalRiemann_eq_slice
    (D : LeafwiseLeviCivitaFamily F S) (p : F.Point) {t : ℝ}
    (ht : F.timeFunction p = t) (u v w z : F.Horizontal p) :
    horizontalRiemann D p u v w z =
      (D.sliceConnection t).curvatureTensor ⟨p, ht⟩
        (((S t).tangentEquiv ⟨p, ht⟩).symm u)
        (((S t).tangentEquiv ⟨p, ht⟩).symm v)
        (((S t).tangentEquiv ⟨p, ht⟩).symm w)
        (((S t).tangentEquiv ⟨p, ht⟩).symm z) := by
  subst t
  rfl

/-- Evaluate horizontal Ricci curvature on an identified actual time slice. -/
theorem horizontalRicci_eq_slice
    (D : LeafwiseLeviCivitaFamily F S) (p : F.Point) {t : ℝ}
    (ht : F.timeFunction p = t) (u v : F.Horizontal p) :
    horizontalRicci D p u v =
      (D.sliceConnection t).ricci ⟨p, ht⟩
        (((S t).tangentEquiv ⟨p, ht⟩).symm u)
        (((S t).tangentEquiv ⟨p, ht⟩).symm v) := by
  subst t
  rfl

/-- Evaluate horizontal scalar curvature on an identified actual time slice. -/
theorem horizontalScalarCurvature_eq_slice
    (D : LeafwiseLeviCivitaFamily F S) (p : F.Point) {t : ℝ}
    (ht : F.timeFunction p = t) :
    horizontalScalarCurvature D p =
      (D.sliceConnection t).scalarCurvature ⟨p, ht⟩ := by
  subst t
  rfl

/-- Evaluate the horizontal curvature norm on an identified actual time slice. -/
theorem horizontalCurvatureNorm_eq_slice
    (D : LeafwiseLeviCivitaFamily F S) (p : F.Point) {t : ℝ}
    (ht : F.timeFunction p = t) :
    horizontalCurvatureNorm D p =
      (D.sliceConnection t).curvatureTensorNorm ⟨p, ht⟩ := by
  subst t
  rfl

end PoincareMT
