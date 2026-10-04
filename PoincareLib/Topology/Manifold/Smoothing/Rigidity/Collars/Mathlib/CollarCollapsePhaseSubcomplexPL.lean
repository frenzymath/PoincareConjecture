import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.Mathlib.CollarCollapsePhasePL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.Mathlib.FiniteLabelSubcomplex

/-!
# Fixed-time collar formulas on a whole phase subcomplex

The finite-label construction supplies an exact vertex-induced carrier
for one phase. Restriction of the fixed-time formulas to that carrier
does not assert that the phase is open in the ambient source, nor does
it construct a real lift of the quotient coordinate.
See rigidity056, sections 1, 2 and 7.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace Y] [T1Space Y]

/-- Restrict a fixed-sign displacement pairing to the exact whole
carrier of one finite label level. -/
theorem finitePiecewiseAffineOn_phase_pair_on_label
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {label : E → Y} (hlabel : ContinuousOn label K.space)
    {D : Set Y} (hD : D.Finite)
    (hlabels : MapsTo label K.space D) (a : Y)
    {u : E → F} {t : E → ℝ}
    (hu : FinitePiecewiseAffineOn u K.space)
    (ht : FinitePiecewiseAffineOn t K.space) (r ε : ℝ) :
    FinitePiecewiseAffineOn
      (fun x => (u x, ε * CollarCollapse.displacement r (t x)))
      (K.vertexSubcomplex {x | label x = a}).space := by
  have hcarrier := K.vertexSubcomplex_space_eq_finite_label
    hlabel hD hlabels a
  have hsub : (K.vertexSubcomplex {x | label x = a}).space ⊆ K.space := by
    rw [hcarrier]
    exact inter_subset_left
  have hfinite : (K.vertexSubcomplex {x | label x = a}).faces.Finite :=
    K.vertexSubcomplex_finite _ hK
  exact (CollarCollapse.finitePiecewiseAffineOn_phase_pair hu ht r ε).restrict
    (K.vertexSubcomplex {x | label x = a}) hfinite hsub

/-- Restrict the collapsed-height pairing to the exact whole carrier of
one finite label level. -/
theorem finitePiecewiseAffineOn_collapse_pair_on_label
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {label : E → Y} (hlabel : ContinuousOn label K.space)
    {D : Set Y} (hD : D.Finite)
    (hlabels : MapsTo label K.space D) (a : Y)
    {u : E → F} {t : E → ℝ}
    (hu : FinitePiecewiseAffineOn u K.space)
    (ht : FinitePiecewiseAffineOn t K.space) (r : ℝ) :
    FinitePiecewiseAffineOn
      (fun x => (u x, CollarCollapse.height r (t x)))
      (K.vertexSubcomplex {x | label x = a}).space := by
  have hcarrier := K.vertexSubcomplex_space_eq_finite_label
    hlabel hD hlabels a
  have hsub : (K.vertexSubcomplex {x | label x = a}).space ⊆ K.space := by
    rw [hcarrier]
    exact inter_subset_left
  have hfinite : (K.vertexSubcomplex {x | label x = a}).faces.Finite :=
    K.vertexSubcomplex_finite _ hK
  exact (CollarCollapse.finitePiecewiseAffineOn_collapse_pair hu ht r).restrict
    (K.vertexSubcomplex {x | label x = a}) hfinite hsub

end Geometry.SimplicialComplex
