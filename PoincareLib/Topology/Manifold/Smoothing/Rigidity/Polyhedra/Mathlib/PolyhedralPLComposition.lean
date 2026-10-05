import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.PolyhedralPLInCharts

/-!
# Finite PL precomposition in the original target charts

Pull each relative target patch back along the actual finite
source map and compose the whole coordinate formulas there.
See Hudson 1969, pp.12--19 and rigidity derivation 007.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F V M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V} {f : F → M} {S : Set F}

/-- Precomposition by an actual finite PL map preserves full
chartwise polyhedral certificates. Every source patch remains
inside the original complete carrier. See derivation 007. -/
theorem PolyhedralPLInCharts.comp_finitePiecewiseAffineOn
    (hf : PolyhedralPLInCharts e f S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → F} (hg : FinitePiecewiseAffineOn g K.space)
    (hmap : MapsTo g K.space S) :
    PolyhedralPLInCharts e (f ∘ g) K.space := by
  refine ⟨hf.continuousOn.comp hg.continuousOn hmap, ?_⟩
  intro x
  obtain ⟨i, J, V0, _, _, hV0, hgxV, hVJ, hfJ, hcoords⟩ :=
    hf.coordinates ⟨g x, hmap x.property⟩
  let gS : K.space → S := fun y => ⟨g y, hmap y.property⟩
  have hgS : Continuous gS := hg.continuousOn.domRestrict.subtype_mk _
  let O : Set K.space := gS ⁻¹' V0
  have hO : IsOpen O := hV0.preimage hgS
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO hgxV
  have hgNJ : MapsTo g N.space J.space := by
    intro y hy
    exact hVJ ⟨gS ⟨y, hNK hy⟩,
      hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy), rfl⟩
  exact ⟨i, N, W, hN, hNK, hW, hxW, hWN,
    fun y hy => hfJ (hgNJ hy),
    hcoords.comp (hg.restrict N hN hNK) hgNJ⟩

end Geometry
