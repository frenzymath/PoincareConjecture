import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart










set_option autoImplicit false

open Set

namespace Geometry





theorem PolyhedralPLInCharts.finitePiecewiseAffineOn_compatible_chart
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {f : E → X} {S : Set E}
    (hf : PolyhedralPLInCharts e f S) (B : OpenPartialHomeomorph X F)
    (hcompat : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKS : K.space ⊆ S)
    (himage : MapsTo f K.space B.source) :
    FinitePiecewiseAffineOn (B ∘ f) K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  let inc : K.space → S := Set.inclusion hKS
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  obtain ⟨i, N, V, _, _, hV, hxV, hVN, hfi, hcoords⟩ :=
    hf.coordinates (inc x)
  obtain ⟨J, W, hJ, hJK, hW, hxW, hWJ, hJV⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x (hV.preimage hinc) hxV
  have hJN : J.space ⊆ N.space := by
    intro y hy
    have hyV : inc ⟨y, hJK hy⟩ ∈ V := hJV
      (show (⟨y, hJK hy⟩ : K.space) ∈ Subtype.val ⁻¹' J.space from hy)
    exact hVN ⟨inc ⟨y, hJK hy⟩, hyV, rfl⟩
  have hchange := ((mem_piecewiseAffineGroupoid_iff F _).mp (hcompat i)).1
  have hresult := hchange.comp_finitePiecewiseAffineOn (hcoords.restrict J hJ hJN) (by
    intro y hy
    change e i (f y) ∈ (e i).target ∧ (e i).symm (e i (f y)) ∈ B.source
    refine ⟨(e i).mapsTo (hfi (hJN hy)), ?_⟩
    rw [(e i).left_inv (hfi (hJN hy))]
    exact himage (hJK hy))
  have hfixed : FinitePiecewiseAffineOn (B ∘ f) J.space := hresult.congr (by
    intro y hy
    change B ((e i).symm (e i (f y))) = B (f y)
    rw [(e i).left_inv (hfi (hJN hy))])
  obtain ⟨M, hM, hMJ, hformula⟩ := hfixed
  exact ⟨M, W, hM, hW, hxW, fun y hy => hMJ.symm.subset (hWJ hy), hformula⟩

end Geometry
