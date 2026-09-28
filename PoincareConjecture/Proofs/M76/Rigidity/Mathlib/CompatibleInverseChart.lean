import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart

set_option autoImplicit false

open Set

namespace Geometry

variable {E F X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X]

theorem polyhedralPLInCharts_of_compatible_chart_inverse
    (e : ι → OpenPartialHomeomorph X F)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (c : OpenPartialHomeomorph X F)
    (hcompat : ∀ i, c.symm.trans (e i) ∈ piecewiseAffineGroupoid F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → F} (hf : FinitePiecewiseAffineOn f K.space)
    (himage : MapsTo f K.space c.target) :
    PolyhedralPLInCharts e (c.symm ∘ f) K.space := by
  have hfc : ContinuousOn (c.symm ∘ f) K.space :=
    c.symm.continuousOn.comp hf.continuousOn himage
  refine ⟨hfc, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := hcover (c.symm (f x))
  let O : Set K.space := (fun y => c.symm (f y)) ⁻¹' (e i).source
  have hO : IsOpen O := (e i).open_source.preimage hfc.domRestrict
  obtain ⟨N, V, hN, hNK, hV, hxV, hVN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO hxi
  have hNi : MapsTo (c.symm ∘ f) N.space (e i).source := by
    intro y hy
    exact hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)
  have hchange := ((mem_piecewiseAffineGroupoid_iff F _).mp (hcompat i)).1
  have hformula := hchange.comp_finitePiecewiseAffineOn
    (hf.restrict N hN hNK) (fun y hy => ⟨himage (hNK hy), hNi hy⟩)
  exact ⟨i, N, V, hN, hNK, hV, hxV, hVN, hNi, hformula⟩

end Geometry
