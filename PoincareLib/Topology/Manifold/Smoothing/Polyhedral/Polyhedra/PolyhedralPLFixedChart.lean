import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.PolyhedralPLInCharts
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PiecewiseAffineGroupoid

/-!
# Finite polyhedral maps in one actual atlas chart

A whole-image chart gives one finite PL formula, and a finite formula
in that chart gives actual atlas-valued PL coordinates through its
inverse. These are the original-chart operations used for Hamilton's
protected Dehn ball, pp.66--67; see M76 derivation345.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X F}

/-- Express a whole polyhedral map in a specified chart containing its
complete image. Atlas transitions are used only on their actual overlap.
See Hamilton pp.66--67 and M76 derivation345. -/
theorem PolyhedralPLInCharts.finitePiecewiseAffineOn_fixed_chart
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (i0 : ι) (himage : MapsTo f K.space (e i0).source) :
    FinitePiecewiseAffineOn ((e i0) ∘ f) K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, N, V, _, hNK, hV, hxV, hVN, hfi, hcoords⟩ := hf.coordinates x
  have hchange := ((mem_piecewiseAffineGroupoid_iff _ _).mp (hcompat i i0)).1
  have hresult := hchange.comp_finitePiecewiseAffineOn hcoords (by
    intro y hy
    change e i (f y) ∈ (e i).target ∧ (e i).symm (e i (f y)) ∈ (e i0).source
    exact ⟨(e i).mapsTo (hfi hy), by
      rw [(e i).left_inv (hfi hy)]
      exact himage (hNK hy)⟩)
  have hfixed : FinitePiecewiseAffineOn ((e i0) ∘ f) N.space :=
    hresult.congr (by
      intro y hy
      change e i0 ((e i).symm (e i (f y))) = e i0 (f y)
      rw [(e i).left_inv (hfi hy)])
  obtain ⟨J, hJ, hJN, hJF⟩ := hfixed
  exact ⟨J, V, hJ, hV, hxV, fun y hy => hJN.symm.subset (hVN hy), hJF⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A finite PL formula landing wholly in one actual chart target
defines a chartwise PL map through that chart's inverse, on the whole
source polyhedron. See Hamilton pp.66--67 and M76 derivation345. -/
theorem polyhedralPLInCharts_of_one_chart_inverse
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → F} (hf : FinitePiecewiseAffineOn f K.space)
    (i : ι) (himage : MapsTo f K.space (e i).target) :
    PolyhedralPLInCharts e ((e i).symm ∘ f) K.space := by
  refine ⟨(e i).symm.continuousOn.comp hf.continuousOn himage, ?_⟩
  intro x
  refine ⟨i, K, univ, hK, subset_rfl, isOpen_univ, mem_univ _, ?_, ?_, ?_⟩
  · rintro y ⟨z, _, rfl⟩
    exact z.property
  · intro y hy
    exact (e i).map_target (himage hy)
  · exact hf.congr (fun y hy => ((e i).right_inv (himage hy)).symm)

end Geometry
