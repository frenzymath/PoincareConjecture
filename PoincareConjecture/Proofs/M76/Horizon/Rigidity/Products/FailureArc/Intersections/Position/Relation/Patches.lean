import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLEqualityLoci
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false
open Set

namespace Geometry

theorem PolyhedralPLInCharts.exists_finite_common_value_patch
    {E F V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : SimplicialComplex ℝ E) (L : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f K.space) (hg : PolyhedralPLInCharts e g L.space)
    (x : K.space) (y : L.space) (hxy : f x = g y) :
    ∃ (P : SimplicialComplex ℝ (E × F)) (W : Set (K.space × L.space)),
      P.faces.Finite ∧ IsOpen W ∧ (x, y) ∈ W ∧
      P.space ⊆ {z | z.1 ∈ K.space ∧ z.2 ∈ L.space ∧ f z.1 = g z.2} ∧
      ∀ z ∈ W, f z.1 = g z.2 → ((z.1 : E), (z.2 : F)) ∈ P.space := by
  obtain ⟨i, N, V₀, _, _, _, hxV, hVN, hNi, _⟩ := hf.coordinates x
  have hxi : f x ∈ (e i).source := hNi (hVN (mem_image_of_mem Subtype.val hxV))
  have hyi : g y ∈ (e i).source := hxy ▸ hxi
  let O₀ : Set K.space := (fun z => f z) ⁻¹' (e i).source
  let O₁ : Set L.space := (fun z => g z) ⁻¹' (e i).source
  have hO₀ : IsOpen O₀ := (e i).open_source.preimage hf.continuousOn.domRestrict
  have hO₁ : IsOpen O₁ := (e i).open_source.preimage hg.continuousOn.domRestrict
  obtain ⟨A, W₀, hA, hAK, hW₀, hxW, hWA, hAO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO₀ hxi
  obtain ⟨B, W₁, hB, hBL, hW₁, hyW, hWB, hBO⟩ :=
    L.exists_relative_polyhedral_neighborhood hL y hO₁ hyi
  have hAsource {z : E} (hz : z ∈ A.space) : f z ∈ (e i).source :=
    hAO (show (⟨z, hAK hz⟩ : K.space) ∈ Subtype.val ⁻¹' A.space from hz)
  have hBsource {z : F} (hz : z ∈ B.space) : g z ∈ (e i).source :=
    hBO (show (⟨z, hBL hz⟩ : L.space) ∈ Subtype.val ⁻¹' B.space from hz)
  have hfA := (hf.restrict_finite A hA hAK).finitePiecewiseAffineOn_compatible_chart_finite_source
    A hA (e i) (fun k => he k i) (fun _ hz => hAsource hz)
  have hgB := (hg.restrict_finite B hB hBL).finitePiecewiseAffineOn_compatible_chart_finite_source
    B hB (e i) (fun k => he k i) (fun _ hz => hBsource hz)
  obtain ⟨P, hP, hPs⟩ := hfA.exists_finite_product_equalizer hgB
  refine ⟨P, W₀ ×ˢ W₁, hP, hW₀.prod hW₁, ⟨hxW, hyW⟩, ?_, ?_⟩
  · intro z hz
    rw [hPs] at hz
    exact ⟨hAK hz.1, hBL hz.2.1,
      (e i).injOn (hAsource hz.1) (hBsource hz.2.1) hz.2.2⟩
  · intro z hz heq
    rw [hPs]
    exact ⟨hWA (mem_image_of_mem Subtype.val hz.1),
      hWB (mem_image_of_mem Subtype.val hz.2), congrArg (e i) heq⟩

end Geometry
