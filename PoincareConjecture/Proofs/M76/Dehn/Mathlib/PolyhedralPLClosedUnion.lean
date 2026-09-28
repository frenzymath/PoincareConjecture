import PoincareConjecture.Proofs.M76.Wall.Mathlib.CompatibleChartFormula
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set

namespace Geometry

theorem PolyhedralPLInCharts.union_of_finite
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {f : E → X}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hfK : PolyhedralPLInCharts e f K.space)
    (hfL : PolyhedralPLInCharts e f L.space) :
    PolyhedralPLInCharts e f (K.space ∪ L.space) := by
  obtain ⟨U, hU, hUs⟩ := K.exists_finite_triangulation_union L hK hL
  suffices PolyhedralPLInCharts e f U.space by simpa only [hUs] using this
  have hfc : ContinuousOn f U.space := by
    rw [hUs]
    exact hfK.continuousOn.union_of_isClosed hfL.continuousOn
      (K.isCompact_space_of_finite hK).isClosed (L.isCompact_space_of_finite hL).isClosed
  refine ⟨hfc, ?_⟩
  intro x
  have hchart : ∃ i, f x ∈ (e i).source := by
    rcases hUs.subset x.property with hxK | hxL
    · obtain ⟨i, J, V, _, _, _, hxV, hVJ, hfJ, _⟩ :=
        hfK.coordinates ⟨x, hxK⟩
      exact ⟨i, hfJ (hVJ ⟨⟨x, hxK⟩, hxV, rfl⟩)⟩
    · obtain ⟨i, J, V, _, _, _, hxV, hVJ, hfJ, _⟩ :=
        hfL.coordinates ⟨x, hxL⟩
      exact ⟨i, hfJ (hVJ ⟨⟨x, hxL⟩, hxV, rfl⟩)⟩
  obtain ⟨i, hxi⟩ := hchart
  let O : Set U.space := (fun y : U.space => f y) ⁻¹' (e i).source
  have hO : IsOpen O := (e i).open_source.preimage hfc.domRestrict
  obtain ⟨J, V, hJ, hJU, hV, hxV, hVJ, hJO⟩ :=
    U.exists_relative_polyhedral_neighborhood hU x hO hxi
  have himage : MapsTo f J.space (e i).source := by
    intro y hy
    exact hJO (show (⟨y, hJU hy⟩ : U.space) ∈ Subtype.val ⁻¹' J.space from hy)
  obtain ⟨P, hP, hPs⟩ := J.exists_finite_triangulation_inter K hJ hK
  obtain ⟨Q, hQ, hQs⟩ := J.exists_finite_triangulation_inter L hJ hL
  have hPK : P.space ⊆ K.space := fun _ hx => (hPs.subset hx).2
  have hQL : Q.space ⊆ L.space := fun _ hx => (hQs.subset hx).2
  have hPJ : P.space ⊆ J.space := fun _ hx => (hPs.subset hx).1
  have hQJ : Q.space ⊆ J.space := fun _ hx => (hQs.subset hx).1
  have hcoordsP := hfK.finitePiecewiseAffineOn_compatible_chart (e i)
    (fun j => hcompat j i) P hP hPK (himage.mono_left hPJ)
  have hcoordsQ := hfL.finitePiecewiseAffineOn_compatible_chart (e i)
    (fun j => hcompat j i) Q hQ hQL (himage.mono_left hQJ)
  have hcover : P.space ∪ Q.space = J.space := by
    rw [hPs, hQs, ← inter_union_distrib_left, ← hUs]
    exact inter_eq_left.mpr hJU
  refine ⟨i, J, V, hJ, hJU, hV, hxV, hVJ, himage, ?_⟩
  rw [← hcover]
  exact finitePiecewiseAffineOn_union hcoordsP hcoordsQ

end Geometry
