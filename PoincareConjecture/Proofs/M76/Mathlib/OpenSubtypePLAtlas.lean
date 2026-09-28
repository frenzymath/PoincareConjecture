import PoincareConjecture.Proofs.M76.Mathlib.CoveringPLAtlas










set_option autoImplicit false

open Set Geometry

namespace Geometry





theorem PolyhedralPLInCharts.exists_open_restriction
    {D E M ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M E}
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (S : SimplicialComplex ℝ D) (hS : S.faces.Finite)
    {f : D → M} (hf : PolyhedralPLInCharts e f S.space)
    (v0 : S.space) {O : Set M} (hO : IsOpen O) (hfO : MapsTo f S.space O) :
    ∃ (d : ι × O → OpenPartialHomeomorph O E) (g : D → O),
      (∀ x, ∃ k, x ∈ (d k).source) ∧
      (∀ k l, (d k).symm.trans (d l) ∈ piecewiseAffineGroupoid E) ∧
      (∀ k, (d k).target ⊆ (e k.1).target) ∧
      (∀ k, (d k : O → E) = (e k.1) ∘ Subtype.val) ∧
      (∀ k, EqOn (Subtype.val ∘ (d k).symm) (e k.1).symm (d k).target) ∧
      PolyhedralPLInCharts d g S.space ∧
      EqOn (Subtype.val ∘ g) f S.space ∧
      g '' S.space = {x : O | (x : M) ∈ f '' S.space} := by
  classical
  obtain ⟨d, hdcover, hdcenter, _, hdtarget, hdval, hdinv, hdcompat⟩ :=
    hO.isOpenEmbedding_subtypeVal.isLocalHomeomorph.exists_piecewiseAffine_coordinate_cover_over
      e hcover hcompat
  let g : D → O := fun x => if hx : x ∈ S.space then ⟨f x, hfO hx⟩
    else ⟨f v0, hfO v0.property⟩
  have hgf : EqOn (Subtype.val ∘ g) f S.space := by
    intro x hx
    simp only [Function.comp_apply, g, dif_pos hx]
  have hgc : ContinuousOn g S.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun x : S.space => (g x : M)) :=
      hf.continuousOn.domRestrict.congr (fun x => (hgf x.property).symm)
    exact hc.subtype_mk (fun x => (g x).property)
  have hg : PolyhedralPLInCharts d g S.space := hf.lift d
    (fun i x => (hdcenter i x).mpr) (fun k x _ => congrFun (hdval k) x) S hS hgc hgf
  refine ⟨d, g, hdcover, hdcompat, hdtarget, hdval, hdinv, hg, hgf, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (hgf hy).symm⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, Subtype.ext ((hgf hy).trans hyx)⟩

end Geometry
