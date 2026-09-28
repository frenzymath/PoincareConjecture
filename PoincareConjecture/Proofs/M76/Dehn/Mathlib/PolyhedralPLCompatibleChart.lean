import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid










set_option autoImplicit false

open Set

namespace Geometry





theorem PolyhedralPLInCharts.finitePiecewiseAffineOn_compatible_chart_finite_source
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (himage : MapsTo f K.space Q.source) :
    FinitePiecewiseAffineOn (Q ∘ f) K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, N, V, _, hNK, hV, hxV, hVN, hfi, hcoords⟩ := hf.coordinates x
  have hchange := ((mem_piecewiseAffineGroupoid_iff F _).mp (hQ i)).1
  have hresult := hchange.comp_finitePiecewiseAffineOn hcoords (by
    intro y hy
    change e i (f y) ∈ (e i).target ∧ (e i).symm (e i (f y)) ∈ Q.source
    refine ⟨(e i).mapsTo (hfi hy), ?_⟩
    rw [(e i).left_inv (hfi hy)]
    exact himage (hNK hy))
  have hfixed : FinitePiecewiseAffineOn (Q ∘ f) N.space := hresult.congr (by
    intro y hy
    change Q ((e i).symm (e i (f y))) = Q (f y)
    rw [(e i).left_inv (hfi hy)])
  obtain ⟨J, hJ, hJN, hJF⟩ := hfixed
  exact ⟨J, V, hJ, hV, hxV, fun y hy => hJN.symm.subset (hVN hy), hJF⟩

end Geometry
