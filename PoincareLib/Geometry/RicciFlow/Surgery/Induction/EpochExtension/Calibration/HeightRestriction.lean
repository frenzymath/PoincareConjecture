import PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornSelection

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Shrink the same geometric selector to satisfy a positive linear bound
in rho and a positive absolute height bound, as required in Chapter 15. -/
noncomputable def M32DeepHornScaleSelection.restrictHeight
    {epsilon C analyticConstant : ℝ}
    (S : M32DeepHornScaleSelection.{u} epsilon C analyticConstant)
    (factor bound : ℝ) (hfactor : 0 < factor) (hbound : 0 < bound) :
    M32DeepHornScaleSelection.{u} epsilon C analyticConstant where
  h := fun rho delta => min (S.h rho delta) (min (factor * rho) bound)
  h_pos := fun rho delta hr hd =>
    lt_min (S.h_pos rho delta hr hd) (lt_min (mul_pos hfactor hr) hbound)
  h_le := fun rho delta hr hd =>
    (min_le_left _ _).trans (S.h_le rho delta hr hd)
  h_mono_rho := by
    intro delta hd rho hr rho' hr' hle
    exact min_le_min (S.h_mono_rho delta hd hr hr' hle)
      (min_le_min (mul_le_mul_of_nonneg_left hle hfactor.le) le_rfl)
  h_mono_delta := by
    intro rho hr delta hd delta' hd' hle
    exact min_le_min (S.h_mono_delta rho hr hd hd' hle) le_rfl
  h_upper := fun rho delta hr hd =>
    (min_le_left _ _).trans (S.h_upper rho delta hr hd)
  deep_horn := by
    intro rho delta a hr hd ha hle
    exact S.deep_horn rho delta a hr hd ha (hle.trans (min_le_left _ _))

/-- The restricted selector satisfies the prescribed linear radius bound. -/
theorem M32DeepHornScaleSelection.restrictHeight_le_radius
    {epsilon C analyticConstant : ℝ}
    (S : M32DeepHornScaleSelection.{u} epsilon C analyticConstant)
    (factor bound : ℝ) (hfactor : 0 < factor) (hbound : 0 < bound)
    (rho delta : ℝ) :
    (S.restrictHeight factor bound hfactor hbound).h rho delta ≤ factor * rho :=
  (min_le_right _ _).trans (min_le_left _ _)

/-- The restricted selector satisfies the prescribed absolute height bound. -/
theorem M32DeepHornScaleSelection.restrictHeight_le_bound
    {epsilon C analyticConstant : ℝ}
    (S : M32DeepHornScaleSelection.{u} epsilon C analyticConstant)
    (factor bound : ℝ) (hfactor : 0 < factor) (hbound : 0 < bound)
    (rho delta : ℝ) :
    (S.restrictHeight factor bound hfactor hbound).h rho delta ≤ bound :=
  (min_le_right _ _).trans (min_le_right _ _)

end PoincareMT
