import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart

set_option autoImplicit false

open Set

namespace Geometry

variable {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace X]

theorem polyhedralPLInCharts_of_compatible_inverse
    (e : ι → OpenPartialHomeomorph X F) (B : OpenPartialHomeomorph X F)
    (hcover : ∀ y ∈ B.source, ∃ i, y ∈ (e i).source)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → F} (hf : FinitePiecewiseAffineOn f K.space)
    (himage : MapsTo f K.space B.target) :
    PolyhedralPLInCharts e (B.symm ∘ f) K.space := by
  have hc : ContinuousOn (B.symm ∘ f) K.space :=
    B.symm.continuousOn.comp hf.continuousOn himage
  refine ⟨hc, ?_⟩
  intro x
  obtain ⟨i, hxi⟩ := hcover (B.symm (f x)) (B.map_target (himage x.property))
  let O : Set K.space := (fun y => B.symm (f y)) ⁻¹' (e i).source
  have hO : IsOpen O := (e i).open_source.preimage hc.domRestrict
  obtain ⟨J, V, hJ, hJK, hV, hxV, hVJ, hJO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO hxi
  have hJi : MapsTo (B.symm ∘ f) J.space (e i).source := by
    intro y hy
    exact hJO (show (⟨y, hJK hy⟩ : K.space) ∈ Subtype.val ⁻¹' J.space from hy)
  have hchange : LocallyPiecewiseAffineOn (B.symm.trans (e i))
      (B.symm.trans (e i)).source := by
    have hrev := (piecewiseAffineGroupoid F).symm (hB i)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using
      ((mem_piecewiseAffineGroupoid_iff F _).mp hrev).1
  have hcoords := hchange.comp_finitePiecewiseAffineOn (hf.restrict J hJ hJK)
    (fun y hy => ⟨himage (hJK hy), hJi hy⟩)
  exact ⟨i, J, V, hJ, hJK, hV, hxV, hVJ, hJi, hcoords⟩

omit [FiniteDimensional ℝ E] in

theorem locallyPiecewiseAffineOn_inverse_normal_coordinates
    (e : ι → OpenPartialHomeomorph X F) (B : OpenPartialHomeomorph X F)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid F)
    (T : E ≃ᴬ[ℝ] F) (i : ι) :
    LocallyPiecewiseAffineOn (T.symm ∘ B ∘ (e i).symm)
      ((e i).symm.trans B).source := by
  have hchange := ((mem_piecewiseAffineGroupoid_iff F _).mp (hB i)).1
  have h := (locallyPiecewiseAffineOn_affine T.symm.toContinuousAffineMap
    isOpen_univ).comp hchange
  simpa only [preimage_univ, inter_univ, OpenPartialHomeomorph.coe_trans,
    Function.comp_assoc, ContinuousAffineEquiv.coe_toContinuousAffineMap] using h

end Geometry
