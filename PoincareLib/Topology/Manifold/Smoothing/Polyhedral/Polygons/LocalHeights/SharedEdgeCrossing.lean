import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.RegularTriangleIntersection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.DoubleCurve.StrictCrossingPointIncidence

/-!
# Crossing points for different local heights

Two affine local heights with the same zero set on an original edge
give the same strict crossing and the same geometric point. Their
values and sign conventions need not agree.
-/

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Equality of zero sets on the literal edge transports strict straddling.
This requires no equality between the two affine height values. -/
theorem StraddlesZero.of_zero_set_eq {A B : E →ᵃ[ℝ] ℝ} {e : Finset E}
    (he : A.StraddlesZero e)
    (hzero : ∀ x ∈ convexHull ℝ (e : Set E), A x = 0 ↔ B x = 0) :
    B.StraddlesZero e := by
  have hp := A.straddlingPoint_mem e he
  apply B.straddlesZero_of_regular_zero he.card ?_ hp.1 ((hzero _ hp.1).mp hp.2)
  intro v hv hBv
  exact he.ne_zero hv ((hzero v (subset_convexHull ℝ (e : Set E) hv)).mpr hBv)

/-- Compatible local zero sets select exactly the same original-edge point. -/
theorem straddlingPoint_eq_of_zero_set_eq {A B : E →ᵃ[ℝ] ℝ} {e : Finset E}
    (hA : A.StraddlesZero e) (hB : B.StraddlesZero e)
    (hzero : ∀ x ∈ convexHull ℝ (e : Set E), A x = 0 ↔ B x = 0) :
    A.straddlingPoint e hA = B.straddlingPoint e hB := by
  have hp := B.straddlingPoint_mem e hB
  exact (StraddlesZero.existsUnique A hA).unique (A.straddlingPoint_mem e hA)
    ⟨hp.1, (hzero _ hp.1).mpr hp.2⟩

/-- Construct the second strict crossing and its equality with the first
from zero-set agreement on the actual edge. -/
theorem exists_straddlingPoint_eq_of_zero_set_eq {A B : E →ᵃ[ℝ] ℝ} {e : Finset E}
    (hA : A.StraddlesZero e)
    (hzero : ∀ x ∈ convexHull ℝ (e : Set E), A x = 0 ↔ B x = 0) :
    ∃ hB : B.StraddlesZero e, A.straddlingPoint e hA = B.straddlingPoint e hB :=
  ⟨hA.of_zero_set_eq hzero, straddlingPoint_eq_of_zero_set_eq hA _ hzero⟩

end AffineMap
