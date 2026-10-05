import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.Mathlib.CollarCollapsePhaseSubcomplexPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLComposition

/-!
# Original-chart PL certificates for a fixed phase collapse

The source collapse is composed with the already certified original
product on one complete label carrier. The signed displacement is
returned separately for the target translation adapter. Neither result
asserts a global lift, a joint PL homotopy, or ambient openness of the
phase carrier. See rigidity056, sections 2, 5 and 7.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F V M ι Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M]
  [TopologicalSpace Y] [T1Space Y]

/-- On one exact finite phase carrier, compose the original-atlas PL
certificate of a product map with the fixed-time source collapse and
retain the signed displacement as a finite PL scalar. The carrier,
phase label, and source membership are supplied by the actual product;
no global source lift or homotopy-time PL statement is claimed. -/
theorem PolyhedralPLInCharts.comp_phase_collapse_displacement_on_label
    {e : ι → OpenPartialHomeomorph M V}
    {C : F × ℝ → M} {S : Set (F × ℝ)}
    (hC : PolyhedralPLInCharts e C S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {label : E → Y} (hlabel : ContinuousOn label K.space)
    {D : Set Y} (hD : D.Finite)
    (hlabels : MapsTo label K.space D) (a : Y)
    {u : E → F} {t : E → ℝ}
    (hu : FinitePiecewiseAffineOn u K.space)
    (ht : FinitePiecewiseAffineOn t K.space) (r ε : ℝ)
    (hmap : MapsTo
      (fun x => (u x, CollarCollapse.height r (t x)))
      (K.vertexSubcomplex {x | label x = a}).space S) :
    PolyhedralPLInCharts e
        (C ∘ fun x => (u x, CollarCollapse.height r (t x)))
        (K.vertexSubcomplex {x | label x = a}).space ∧
      FinitePiecewiseAffineOn
        (fun x => ε * CollarCollapse.displacement r (t x))
        (K.vertexSubcomplex {x | label x = a}).space := by
  have hJ : (K.vertexSubcomplex {x | label x = a}).faces.Finite :=
    K.vertexSubcomplex_finite _ hK
  have hcollapse :
      FinitePiecewiseAffineOn
        (fun x => (u x, CollarCollapse.height r (t x)))
        (K.vertexSubcomplex {x | label x = a}).space :=
    SimplicialComplex.finitePiecewiseAffineOn_collapse_pair_on_label
      K hK hlabel hD hlabels a hu ht r
  have hcarrier := K.vertexSubcomplex_space_eq_finite_label
    hlabel hD hlabels a
  have hsub : (K.vertexSubcomplex {x | label x = a}).space ⊆ K.space := by
    rw [hcarrier]
    exact inter_subset_left
  have htJ : FinitePiecewiseAffineOn t
      (K.vertexSubcomplex {x | label x = a}).space :=
    ht.restrict _ hJ hsub
  have hdisplacement :=
    CollarCollapse.finitePiecewiseAffineOn_scaled_displacement htJ r ε
  refine ⟨hC.comp_finitePiecewiseAffineOn _ hJ hcollapse hmap, hdisplacement⟩

end Geometry
