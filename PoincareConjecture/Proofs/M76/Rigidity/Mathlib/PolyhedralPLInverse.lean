import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInverseChart

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace X]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in

theorem PolyhedralPLInCharts.restrict_finite
    {e : ι → OpenPartialHomeomorph X F} {f : E → X} {S : Set E}
    (hf : PolyhedralPLInCharts e f S)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKS : K.space ⊆ S) :
    PolyhedralPLInCharts e f K.space := by
  refine ⟨hf.continuousOn.mono hKS, ?_⟩
  intro x
  obtain ⟨i, J, V, _, hJS, hV, hxV, hVJ, hfJ, hcoords⟩ :=
    hf.coordinates ⟨x, hKS x.property⟩
  let q : K.space → S := fun y => ⟨y, hKS y.property⟩
  have hq : Continuous q := continuous_subtype_val.subtype_mk _
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNV⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x (hV.preimage hq) hxV
  have hNJ : N.space ⊆ J.space := by
    intro y hy
    exact hVJ ⟨q ⟨y, hNK hy⟩,
      hNV (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy), rfl⟩
  exact ⟨i, N, W, hN, hNK, hW, hxW, hWN,
    fun y hy => hfJ (hNJ hy), hcoords.restrict N hN hNJ⟩

theorem PolyhedralPLInCharts.finitePiecewiseAffineOn_lift
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {f : E → X} {S : Set E} (hf : PolyhedralPLInCharts e f S)
    (hinj : InjOn f S) (K : SimplicialComplex ℝ G) (hK : K.faces.Finite)
    {q : G → E} (hq : ContinuousOn q K.space) (hqS : MapsTo q K.space S)
    (hfq : PolyhedralPLInCharts e (f ∘ q) K.space) :
    FinitePiecewiseAffineOn q K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, J, V, _, hJS, hV, hqxV, hVJ, hfJ, hcoords⟩ :=
    hf.coordinates ⟨q x, hqS x.property⟩
  obtain ⟨j, L, W, _, hLK, hW, hxW, hWL, hfqL, hcomposite⟩ := hfq.coordinates x
  let qS : K.space → S := fun y => ⟨q y, hqS y.property⟩
  have hqSc : Continuous qS := hq.domRestrict.subtype_mk _
  let O : Set K.space := W ∩ qS ⁻¹' V
  have hO : IsOpen O := hW.inter (hV.preimage hqSc)
  obtain ⟨N, W', hN, hNK, hW', hxW', hW'N, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hxW, hqxV⟩
  have hNL : N.space ⊆ L.space := by
    intro y hy
    exact hWL ⟨⟨y, hNK hy⟩,
      (hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).1, rfl⟩
  have hqJ : MapsTo q N.space J.space := by
    intro y hy
    exact hVJ ⟨qS ⟨y, hNK hy⟩,
      (hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).2, rfl⟩
  have hfi : InjOn ((e i) ∘ f) J.space := by
    intro y hy z hz heq
    exact hinj (hJS hy) (hJS hz) ((e i).injOn (hfJ hy) (hfJ hz) heq)
  obtain ⟨b, hb, hbval⟩ := hcoords.exists_homeomorph_image hfi
  obtain ⟨r, hr, hrval⟩ := hb.symm
  have hrleft (y : E) (hy : y ∈ J.space) : r (e i (f y)) = y := by
    have h := hrval (b ⟨y, hy⟩)
    rw [b.symm_apply_apply] at h
    simpa only [hbval, Function.comp_apply] using h.symm
  have hjleft (y : G) (hy : y ∈ N.space) :
      (e j).symm (e j (f (q y))) = f (q y) := by
    simpa only [Function.comp_apply] using (e j).left_inv (hfqL (hNL hy))
  have hchange := ((mem_piecewiseAffineGroupoid_iff F _).mp (hcompat j i)).1
  have hchanged := hchange.comp_finitePiecewiseAffineOn
    (hcomposite.restrict N hN hNL) (by
      intro y hy
      change e j (f (q y)) ∈ (e j).target ∧
        (e j).symm (e j (f (q y))) ∈ (e i).source
      refine ⟨(e j).map_source (hfqL (hNL hy)), ?_⟩
      rw [hjleft y hy]
      exact hfJ (hqJ hy))
  have hactual : FinitePiecewiseAffineOn (fun y => e i (f (q y))) N.space :=
    hchanged.congr (by
      intro y hy
      change e i ((e j).symm (e j (f (q y)))) = e i (f (q y))
      rw [hjleft y hy])
  have hmap : MapsTo (fun y => e i (f (q y))) N.space (((e i) ∘ f) '' J.space) := by
    intro y hy
    exact ⟨q y, hqJ hy, rfl⟩
  have hqN : FinitePiecewiseAffineOn q N.space :=
    (hr.comp hactual hmap).congr (fun y hy => hrleft (q y) (hqJ hy))
  obtain ⟨R, hR, hRN, hqR⟩ := hqN
  exact ⟨R, W', hR, hW', hxW', fun y hy => hRN.symm.subset (hW'N hy), hqR⟩

end Geometry
