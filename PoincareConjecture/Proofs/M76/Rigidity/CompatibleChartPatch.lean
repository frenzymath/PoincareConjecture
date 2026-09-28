import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid









set_option autoImplicit false

open Set

namespace Geometry

variable {E V X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}





theorem PolyhedralPLInCharts.exists_finite_compatible_chart_patch
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (G : OpenPartialHomeomorph X V)
    (hcompat : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V)
    (x : K.space) (hxG : f x ∈ G.source) :
    ∃ (N : SimplicialComplex ℝ E) (W : Set K.space),
      N.faces.Finite ∧ N.space ⊆ K.space ∧ IsOpen W ∧ x ∈ W ∧
      Subtype.val '' W ⊆ N.space ∧ MapsTo f N.space G.source ∧
      FinitePiecewiseAffineOn (G ∘ f) N.space := by
  obtain ⟨i, J, U, _, _, hU, hxU, hUJ, hfi, hcoords⟩ := hf.coordinates x
  let O : Set K.space := U ∩ (fun y => f y) ⁻¹' G.source
  have hO : IsOpen O := hU.inter (G.open_source.preimage hf.continuousOn.domRestrict)
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hxU, hxG⟩
  have hNJ : N.space ⊆ J.space := by
    intro y hy
    exact hUJ ⟨⟨y, hNK hy⟩,
      (hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).1,
      rfl⟩
  have hNG : MapsTo f N.space G.source := by
    intro y hy
    exact (hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).2
  have hchange := ((mem_piecewiseAffineGroupoid_iff V _).mp (hcompat i)).1
  have hresult := hchange.comp_finitePiecewiseAffineOn (hcoords.restrict N hN hNJ) (by
    intro y hy
    change e i (f y) ∈ (e i).target ∧ (e i).symm (e i (f y)) ∈ G.source
    refine ⟨(e i).map_source (hfi (hNJ hy)), ?_⟩
    rw [(e i).left_inv (hfi (hNJ hy))]
    exact hNG hy)
  refine ⟨N, W, hN, hNK, hW, hxW, hWN, hNG, hresult.congr ?_⟩
  intro y hy
  change G ((e i).symm (e i (f y))) = G (f y)
  rw [(e i).left_inv (hfi (hNJ hy))]

end Geometry
