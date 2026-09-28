import PoincareConjecture.Proofs.M76.Mathlib.RelativeManifoldPLApproximation
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polyhedra.ControlledPolyhedronApproximation










set_option autoImplicit false

open Set Geometry unitInterval

namespace OpenPartialHomeomorph

theorem exists_relative_polyhedralPL_approximation_with_compact_control
    {E F M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    (e : ι → OpenPartialHomeomorph M F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hLK : L.space ⊆ K.space) {f : E → M} (hf : ContinuousOn f K.space)
    (hfL : PolyhedralPLInCharts e f L.space)
    {W : Set M} (hW : IsOpen W) (hfW : MapsTo f K.space W)
    {B : Set E} (hB : IsCompact B) (hBK : B ⊆ K.space)
    {V : Set M} (hV : IsOpen V) (hfV : MapsTo f B V) :
    ∃ q : E → M, PolyhedralPLInCharts e q K.space ∧ EqOn q f L.space ∧
      MapsTo q K.space W ∧
      ∃ R : C(I × K.space, M), (∀ z, R z ∈ W) ∧
        (∀ x : K.space, R (0, x) = f x) ∧
        (∀ x : K.space, R (1, x) = q x) ∧
        (∀ (t : I) (x : K.space), (x : E) ∈ L.space → R (t, x) = f x) ∧
        ∀ (t : I) (x : K.space), (x : E) ∈ B → R (t, x) ∈ V := by
  classical
  have hA : IsCompact (f '' K.space) :=
    (K.isCompact_space_of_finite hK).image_of_continuousOn hf
  obtain ⟨s, Fmap, C, J, H, _, hAC, hCW, hJ, hFc, hFPL, hH, hcharts⟩ :=
    exists_compact_PL_neighborhood_model e hcompat hcover hA hW hfW.image_subset
  have hfC : MapsTo f K.space C := fun x hx =>
    interior_subset (hAC (mem_image_of_mem f hx))
  have hfJ : MapsTo (Fmap ∘ f) K.space J.space := by
    intro x hx
    rw [Function.comp_apply, ← hH ⟨f x, hfC hx⟩]
    exact (H ⟨f x, hfC hx⟩).property
  have hFfL : FinitePiecewiseAffineOn (Fmap ∘ f) L.space :=
    hfL.finitePiecewiseAffineOn_comp L hL hFPL
  let O : Set J.space := (fun z => (H.symm z : M)) ⁻¹' V
  have hO : IsOpen O := hV.preimage (continuous_subtype_val.comp H.symm.continuous)
  obtain ⟨V0, hV0, hV0eq⟩ := isOpen_induced_iff.mp hO
  have hfV0 : MapsTo (Fmap ∘ f) B V0 := by
    intro x hx
    have hz : (⟨Fmap (f x), hfJ (hBK hx)⟩ : J.space) = H ⟨f x, hfC (hBK hx)⟩ :=
      Subtype.ext (hH ⟨f x, hfC (hBK hx)⟩).symm
    change (⟨Fmap (f x), hfJ (hBK hx)⟩ : J.space) ∈ Subtype.val ⁻¹' V0
    rw [hV0eq]
    change (H.symm ⟨Fmap (f x), hfJ (hBK hx)⟩ : M) ∈ V
    rw [hz, H.symm_apply_apply]
    exact hfV hx
  obtain ⟨g, hg, hgfix, hgJ, T, hTJ, hT0, hT1, hTfix, hTcontrol⟩ :=
    K.exists_relative_finitePL_map_to_polyhedron_with_compact_control J hK hJ
      (hFc.comp_continuousOn hf) hfJ hLK hFfL hB hBK hV0 hfV0
  let q : E → M := fun x => if hx : x ∈ K.space then
    (H.symm ⟨g x, hgJ hx⟩ : M) else f x
  have hq (x : E) (hx : x ∈ K.space) :
      q x = (H.symm ⟨g x, hgJ hx⟩ : M) := by simp only [q, dif_pos hx]
  have hgc : Continuous (fun x : K.space => (⟨g x, hgJ x.property⟩ : J.space)) :=
    (hg.continuousOn.comp_continuous continuous_subtype_val
      (fun x => x.property)).subtype_mk _
  have hqc : ContinuousOn q K.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp (H.symm.continuous.comp hgc)).congr
      (fun x => (hq x x.property).symm)
  have hqC : MapsTo q K.space C := by
    intro x hx
    rw [hq x hx]
    exact (H.symm ⟨g x, hgJ hx⟩).property
  have hFq : EqOn (Fmap ∘ q) g K.space := by
    intro x hx
    change Fmap (q x) = g x
    rw [hq x hx]
    exact (hH (H.symm ⟨g x, hgJ hx⟩)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨g x, hgJ hx⟩))
  have hqPL : PolyhedralPLInCharts e q K.space :=
    polyhedralPLInCharts_of_affine_projections e Fmap C hcharts K hK hqc hqC hg hFq
  have hHinv (x : E) (hx : x ∈ K.space) (z : J.space)
      (hz : (z : s → ℝ × F) = Fmap (f x)) : (H.symm z : M) = f x := by
    have hzH : z = H ⟨f x, hfC hx⟩ :=
      Subtype.ext (hz.trans (hH ⟨f x, hfC hx⟩).symm)
    rw [hzH, H.symm_apply_apply]
  let R : C(I × K.space, M) :=
    ⟨fun z => (H.symm ⟨T z, hTJ z⟩ : M),
      continuous_subtype_val.comp (H.symm.continuous.comp
        (T.continuous.subtype_mk hTJ))⟩
  refine ⟨q, hqPL, ?_, fun x hx => hCW (hqC hx), R, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hq x (hLK hx)]
    exact hHinv x (hLK hx) ⟨g x, hgJ (hLK hx)⟩ (hgfix hx)
  · intro z
    exact hCW (H.symm ⟨T z, hTJ z⟩).property
  · intro x
    exact hHinv x x.property ⟨T (0, x), hTJ (0, x)⟩ (hT0 x)
  · intro x
    change (H.symm ⟨T (1, x), hTJ (1, x)⟩ : M) = q x
    rw [hq x x.property]
    exact congrArg (fun z : J.space => (H.symm z : M)) (Subtype.ext (hT1 x))
  · intro t x hx
    exact hHinv x x.property ⟨T (t, x), hTJ (t, x)⟩ (hTfix t x hx)
  · intro t x hx
    have hz : (⟨T (t, x), hTJ (t, x)⟩ : J.space) ∈ Subtype.val ⁻¹' V0 :=
      hTcontrol t x hx
    rw [hV0eq] at hz
    exact hz

end OpenPartialHomeomorph
