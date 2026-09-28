import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLEqualityLoci
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false

open Set

namespace Geometry

theorem PolyhedralPLInCharts.exists_finite_double_pair_patch
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (x y : K.space) (hxy : f x = f y) (hne : x ≠ y) :
    ∃ (L : SimplicialComplex ℝ (E × E)) (W : Set (K.space × K.space)),
      L.faces.Finite ∧ IsOpen W ∧ (x, y) ∈ W ∧
      L.space ⊆ {z | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
        f z.1 = f z.2 ∧ z.1 ≠ z.2} ∧
      ∀ z ∈ W, f z.1 = f z.2 → ((z.1 : E), (z.2 : E)) ∈ L.space := by
  obtain ⟨i, N, V, _, _, _, hxV, hVN, hNi, _⟩ := hf.coordinates x
  have hxi : f x ∈ (e i).source := hNi (hVN (mem_image_of_mem Subtype.val hxV))
  have hyi : f y ∈ (e i).source := hxy ▸ hxi
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ :=
    t2_separation (show (x : E) ≠ (y : E) from fun h => hne (Subtype.ext h))
  let O : Set K.space := (fun z => f z) ⁻¹' (e i).source
  have hO : IsOpen O := (e i).open_source.preimage hf.continuousOn.domRestrict
  obtain ⟨P, W₁, hP, hPK, hW₁, hxW₁, hW₁P, hPO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x
      ((hU.preimage continuous_subtype_val).inter hO) ⟨hxU, hxi⟩
  obtain ⟨Q, W₂, hQ, hQK, hW₂, hyW₂, hW₂Q, hQO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK y
      ((hV.preimage continuous_subtype_val).inter hO) ⟨hyV, hyi⟩
  have hPsource {z : E} (hz : z ∈ P.space) : z ∈ U ∧ f z ∈ (e i).source :=
    hPO (show (⟨z, hPK hz⟩ : K.space) ∈ Subtype.val ⁻¹' P.space from hz)
  have hQsource {z : E} (hz : z ∈ Q.space) : z ∈ V ∧ f z ∈ (e i).source :=
    hQO (show (⟨z, hQK hz⟩ : K.space) ∈ Subtype.val ⁻¹' Q.space from hz)
  have hfPbase := hf.restrict_finite P hP hPK
  have hfP := hfPbase.finitePiecewiseAffineOn_compatible_chart_finite_source P hP (e i)
      (fun k => he k i) (fun z hz => (hPsource hz).2)
  have hfQbase := hf.restrict_finite Q hQ hQK
  have hfQ := hfQbase.finitePiecewiseAffineOn_compatible_chart_finite_source Q hQ (e i)
      (fun k => he k i) (fun z hz => (hQsource hz).2)
  obtain ⟨L, hL, hLs⟩ := hfP.exists_finite_product_equalizer hfQ
  refine ⟨L, W₁ ×ˢ W₂, hL, hW₁.prod hW₂, ⟨hxW₁, hyW₂⟩, ?_, ?_⟩
  · intro z hz
    rw [hLs] at hz
    refine ⟨hPK hz.1, hQK hz.2.1,
      (e i).injOn (hPsource hz.1).2 (hQsource hz.2.1).2 hz.2.2, ?_⟩
    intro heq
    exact Set.disjoint_left.mp hUV (hPsource hz.1).1
      (heq.symm ▸ (hQsource hz.2.1).1)
  · intro z hz heq
    rw [hLs]
    exact ⟨hW₁P (mem_image_of_mem Subtype.val hz.1),
      hW₂Q (mem_image_of_mem Subtype.val hz.2), congrArg (e i) heq⟩

end Geometry
