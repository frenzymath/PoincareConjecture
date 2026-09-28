import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MixedCompatibleChartPatch








set_option autoImplicit false

open Set Geometry Topology

namespace Geometry

theorem PolyhedralPLInCharts.locallyPiecewiseAffineOn_mixed_chart_comp_interior
    {E V W X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    {j : E → X} {K : SimplicialComplex ℝ E}
    (hj : PolyhedralPLInCharts e j K.space) (hK : K.faces.Finite)
    (Q : OpenPartialHomeomorph X W)
    (hcompat : ∀ i, LocallyPiecewiseAffineOn
      ((e i).symm.trans Q) ((e i).symm.trans Q).source) :
    LocallyPiecewiseAffineOn (Q ∘ j) (interior K.space ∩ j ⁻¹' Q.source) := by
  have hopen : IsOpen (interior K.space ∩ j ⁻¹' Q.source) :=
    (hj.continuousOn.mono interior_subset).isOpen_inter_preimage
      isOpen_interior Q.open_source
  intro x hx
  obtain ⟨N, U, _, _, hU, hxU, hUN, _, hfinite⟩ :=
    hj.exists_finite_mixed_chart_patch K hK Q hcompat ⟨x, interior_subset hx.1⟩ hx.2
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
  have hxO : x ∈ O := by
    have h := hxU
    rw [← hOU] at h
    exact h
  have hxN : x ∈ interior N.space := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset ((hO.inter isOpen_interior).mem_nhds ⟨hxO, hx.1⟩)
    intro y hy
    apply hUN
    refine ⟨⟨y, interior_subset hy.2⟩, ?_, rfl⟩
    rw [← hOU]
    exact hy.1
  obtain ⟨L, hL, hLN, hcoordinates⟩ := hfinite
  have hxL : x ∈ interior L.space := hLN.symm ▸ hxN
  obtain ⟨T, hT, hxT, hTU, hcoords⟩ := hcoordinates.exists_finite_neighborhood hL
    isCompact_singleton hopen (singleton_subset_iff.mpr ⟨hxL, hx⟩)
  exact ⟨T, hT, hxT (mem_singleton x), fun _ hy => (hTU hy).2, hcoords⟩

theorem PolyhedralPLInCharts.locallyPiecewiseAffineOn_tangent_chart_comp_interior
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    {j : E → X} {K : SimplicialComplex ℝ E}
    (hj : PolyhedralPLInCharts e j K.space) (hK : K.faces.Finite)
    (Q : OpenPartialHomeomorph X ((ℝ × ℝ) × ℝ))
    (hcompat : ∀ i, LocallyPiecewiseAffineOn
      ((e i).symm.trans Q) ((e i).symm.trans Q).source) :
    LocallyPiecewiseAffineOn (Prod.fst ∘ Q ∘ j)
      (interior K.space ∩ j ⁻¹' Q.source) := by
  have hcoords := hj.locallyPiecewiseAffineOn_mixed_chart_comp_interior hK Q hcompat
  have hprojection := locallyPiecewiseAffineOn_affine
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap isOpen_univ
  simpa using hprojection.comp hcoords

end Geometry
