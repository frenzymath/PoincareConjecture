import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid

set_option autoImplicit false

open Set

namespace Geometry

theorem PolyhedralPLInCharts.comp_chart_homeomorph {E F X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {f : E → X}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hf : PolyhedralPLInCharts e f K.space) (G : X ≃ₜ X)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (hG : ∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid F) :
    PolyhedralPLInCharts e (G ∘ f) K.space := by
  have hcont : ContinuousOn (G ∘ f) K.space := G.continuous.comp_continuousOn hf.continuousOn
  refine ⟨hcont, ?_⟩
  intro x
  obtain ⟨i, J, V, _, _, hV, hxV, hVJ, hfJ, hcoords⟩ := hf.coordinates x
  obtain ⟨j, hxj⟩ := hcover (G (f x))
  let O : Set K.space := V ∩ (fun y => G (f y)) ⁻¹' (e j).source
  have hO : IsOpen O := hV.inter ((e j).open_source.preimage
    (hcont.comp_continuous continuous_subtype_val (fun y => y.property)))
  obtain ⟨L, W, hL, hLK, hW, hxW, hWL, hLO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hxV, hxj⟩
  have hLV (y : E) (hy : y ∈ L.space) : (⟨y, hLK hy⟩ : K.space) ∈ V :=
    (hLO (show (⟨y, hLK hy⟩ : K.space) ∈ Subtype.val ⁻¹' L.space from hy)).1
  have hLj (y : E) (hy : y ∈ L.space) : G (f y) ∈ (e j).source :=
    (hLO (show (⟨y, hLK hy⟩ : K.space) ∈ Subtype.val ⁻¹' L.space from hy)).2
  have hLJ : L.space ⊆ J.space := by
    intro y hy
    exact hVJ ⟨⟨y, hLK hy⟩, hLV y hy, rfl⟩
  let T := (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j))
  have hTPL : LocallyPiecewiseAffineOn T T.source :=
    ((mem_piecewiseAffineGroupoid_iff F T).mp (hG i j)).1
  have hmaps : MapsTo ((e i) ∘ f) L.space T.source := by
    intro y hy
    have hfi : f y ∈ (e i).source := hfJ (hLJ hy)
    refine ⟨(e i).map_source hfi, mem_univ _, ?_⟩
    change G ((e i).symm ((e i) (f y))) ∈ (e j).source
    rw [(e i).left_inv hfi]
    exact hLj y hy
  refine ⟨j, L, W, hL, hLK, hW, hxW, hWL, fun y hy => hLj y hy, ?_⟩
  apply (hTPL.comp_finitePiecewiseAffineOn (hcoords.restrict L hL hLJ) hmaps).congr
  intro y hy
  change (e j) (G ((e i).symm ((e i) (f y)))) = (e j) (G (f y))
  rw [(e i).left_inv (hfJ (hLJ hy))]

end Geometry
