import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDiagram











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} {R : Set X} {T : Set Y} {U : Set R}





theorem ChartwisePLOn.polyhedralPLInCharts_comp
    {d : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {e : κ → OpenPartialHomeomorph Y (Fin 3 → ℝ)}
    {f : C(R, T)} (hf : ChartwisePLOn d e f U)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (q : E → R) (hq : ContinuousOn q K.space)
    (hqPL : PolyhedralPLInCharts d (fun x => (q x : X)) K.space)
    (hqU : MapsTo q K.space U) :
    PolyhedralPLInCharts e (fun x => (f (q x) : Y)) K.space := by
  refine ⟨(continuous_subtype_val.comp f.continuous).comp_continuousOn hq, ?_⟩
  intro x
  obtain ⟨j, J, V, hJ, hJK, hV, hxV, hVJ, hqJ, hqJPL⟩ := hqPL.coordinates x
  obtain ⟨j', i', L, W, F, _, hW, hxW, _, hWd, hWL, _, _, hF, hFval⟩ :=
    hf.coordinates (q x) (hqU x.property)
  let O : Set K.space := V ∩ (fun y : K.space => q y) ⁻¹' W
  have hO : IsOpen O := hV.inter (hW.preimage
    (hq.comp_continuous continuous_subtype_val (fun y => y.property)))
  obtain ⟨N, V', hN, hNK, hV', hxV', hV'N, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hxV, hxW⟩
  have hNJ : N.space ⊆ J.space := by
    intro y hy
    exact hVJ (mem_image_of_mem Subtype.val
      (hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).1)
  have hqW (y : E) (hy : y ∈ N.space) : q y ∈ W :=
    (hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).2
  have hqj (y : E) (hy : y ∈ N.space) : (q y : X) ∈ (d j).source :=
    hqJ (hNJ hy)
  have hqj' (y : E) (hy : y ∈ N.space) : (q y : X) ∈ (d j').source :=
    hWd (hqW y hy)
  have hqL (y : E) (hy : y ∈ N.space) : d j' (q y) ∈ L.space :=
    hWL (mem_image_of_mem ((d j') ∘ (Subtype.val : R → X)) (hqW y hy))
  have hchange := ((mem_piecewiseAffineGroupoid_iff _ _).mp
    (hf.source_domain.compatible j j')).1
  have hcoord := hchange.comp_finitePiecewiseAffineOn
    (hqJPL.restrict N hN hNJ) (by
      intro y hy
      change d j (q y) ∈ (d j).target ∧ (d j).symm (d j (q y)) ∈ (d j').source
      exact ⟨(d j).mapsTo (hqj y hy), by rw [(d j).left_inv (hqj y hy)]; exact hqj' y hy⟩)
  have hqjPL : FinitePiecewiseAffineOn (fun y => d j' (q y)) N.space :=
    hcoord.congr (by
      intro y hy
      change d j' ((d j).symm (d j (q y))) = d j' (q y)
      rw [(d j).left_inv (hqj y hy)])
  refine ⟨i', N, V', hN, hNK, hV', hxV', hV'N, ?_, ?_⟩
  · intro y hy
    exact (hFval (q y) (hqj' y hy) (hqL y hy)).1
  · exact (hF.comp hqjPL hqL).congr (by
      intro y hy
      exact (hFval (q y) (hqj' y hy) (hqL y hy)).2)




theorem ChartwisePLOn.finitePiecewiseAffineOn_fixed_chart
    {d : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {e : κ → OpenPartialHomeomorph Y (Fin 3 → ℝ)}
    {f : C(R, T)} (hf : ChartwisePLOn d e f U)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (q : E → R) (hq : ContinuousOn q K.space)
    (hqPL : PolyhedralPLInCharts d (fun x => (q x : X)) K.space)
    (hqU : MapsTo q K.space U)
    (i0 : κ) (himage : ∀ x ∈ K.space, (f (q x) : Y) ∈ (e i0).source) :
    FinitePiecewiseAffineOn (fun x => e i0 (f (q x))) K.space := by
  have hcomp := hf.polyhedralPLInCharts_comp K hK q hq hqPL hqU
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, N, V, _, hNK, hV, hxV, hVN, hfi, hcoords⟩ := hcomp.coordinates x
  have hchange := ((mem_piecewiseAffineGroupoid_iff _ _).mp
    (hf.target_domain.compatible i i0)).1
  have hresult := hchange.comp_finitePiecewiseAffineOn hcoords (by
    intro y hy
    change e i (f (q y)) ∈ (e i).target ∧
      (e i).symm (e i (f (q y))) ∈ (e i0).source
    exact ⟨(e i).mapsTo (hfi hy), by
      rw [(e i).left_inv (hfi hy)]
      exact himage y (hNK hy)⟩)
  have hfixed : FinitePiecewiseAffineOn (fun y => e i0 (f (q y))) N.space :=
    hresult.congr (by
      intro y hy
      change e i0 ((e i).symm (e i (f (q y)))) = e i0 (f (q y))
      rw [(e i).left_inv (hfi hy)])
  obtain ⟨J, hJ, hJN, hJF⟩ := hfixed
  exact ⟨J, V, hJ, hV, hxV, fun y hy => hJN.symm.subset (hVN hy), hJF⟩

end PoincareConjecture.M76
