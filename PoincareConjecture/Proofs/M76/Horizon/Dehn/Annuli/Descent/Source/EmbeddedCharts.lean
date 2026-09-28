import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Source.Parameters
import PoincareConjecture.Proofs.M76.Rigidity.SourceInteriorPairChart

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_embedded_source_plane_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (hemb : IsEmbedding (fun z : K.space ↦ f z))
    (G : OpenPartialHomeomorph X V3)
    (hcompat : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3)
    (z : K.space) (hzG : f z ∈ G.source)
    (q : OpenPartialHomeomorph K.space V2) (hzq : z ∈ q.source)
    (hqPL : LocallyPiecewiseAffineOn (fun u ↦ (q.symm u : E)) q.target)
    {U : Set X} (hU : IsOpen U) (hfzU : f z ∈ U) :
    ∃ H : OpenPartialHomeomorph X C3,
      f z ∈ H.source ∧ H.source ⊆ U ∩ G.source ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧ H (f z) = 0 ∧
      (∀ x ∈ H.source, x ∈ f '' K.space ↔ (H x).2 = 0) ∧
      ∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source := by
  obtain ⟨N, W, hN, hNK, hW, hzW, hWN, hNG, hcoords⟩ :=
    hf.exists_finite_compatible_chart_patch K hK G hcompat z hzG
  let A := q.target ∩ q.symm ⁻¹' W
  have hA : IsOpen A := q.isOpen_inter_preimage_symm hW
  have hqzA : q z ∈ A := ⟨q.map_source hzq, by
    change q.symm (q z) ∈ W
    rw [q.left_inv hzq]
    exact hzW⟩
  obtain ⟨L, hL, hzL, hLA⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton hA (singleton_subset_iff.mpr hqzA)
  have hzLi : q z ∈ interior L.space := hzL (mem_singleton _)
  let lift : V2 → E := fun u ↦ q.symm u
  have hLN : MapsTo lift L.space N.space :=
    fun u hu ↦ hWN ⟨q.symm u, (hLA hu).2, rfl⟩
  have hLtarget : L.space ⊆ q.target := fun _ hu ↦ (hLA hu).1
  have hPL : FinitePiecewiseAffineOn ((G ∘ f) ∘ lift) L.space :=
    hcoords.comp (hqPL.finitePiecewiseAffineOn L hL hLtarget) hLN
  have hinj : InjOn ((G ∘ f) ∘ lift) L.space := by
    intro u hu v hv huv
    have hfuv : f (lift u) = f (lift v) := G.injOn (hNG (hLN hu)) (hNG (hLN hv)) huv
    have hq : q.symm u = q.symm v := hemb.injective hfuv
    exact q.symm.injOn (hLtarget hu) (hLtarget hv) hq
  let P := lift '' L.space
  have hPK : P ⊆ K.space := by
    rintro _ ⟨u, _, rfl⟩
    exact (q.symm u).property
  have hPG : MapsTo f P G.source := by
    rintro _ ⟨u, hu, rfl⟩
    exact hNG (hLN hu)
  let W' := q.source ∩ q ⁻¹' interior L.space
  have hW' : IsOpen W' := q.isOpen_inter_preimage isOpen_interior
  have hzW' : z ∈ W' := ⟨hzq, hzLi⟩
  have hW'P : Subtype.val '' W' ⊆ P := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨q v, interior_subset hv.2, congrArg Subtype.val (q.left_inv hv.1)⟩
  obtain ⟨O, hO, hzO, hOt, hfull⟩ :=
    hemb.exists_open_chart_image_eq_of_patch G hPK hPG z W' hW' hzW' hW'P
  let V := O ∩ G '' (U ∩ G.source)
  let T := G '' (f '' K.space ∩ G.source)
  have hV : IsOpen V := hO.inter
    (G.isOpen_image_of_subset_source (hU.inter G.open_source) inter_subset_right)
  have hzV : G (f z) ∈ V := ⟨hzO, ⟨f z, ⟨hfzU, hzG⟩, rfl⟩⟩
  have hVt : V ⊆ G.target := fun _ hx ↦ hOt hx.1
  have hliftz : lift (q z) = (z : E) := congrArg Subtype.val (q.left_inv hzq)
  have hfullV : T ∩ V = (((G ∘ f) ∘ lift) '' L.space) ∩ V := by
    have hfull' : T ∩ O = (((G ∘ f) ∘ lift) '' L.space) ∩ O := by
      simpa only [T, P, image_image, Function.comp_def] using hfull
    ext x
    exact ⟨fun hx ↦ ⟨(hfull'.subset ⟨hx.1, hx.2.1⟩).1, hx.2⟩,
      fun hx ↦ ⟨(hfull'.symm.subset ⟨hx.1, hx.2.1⟩).1, hx.2⟩⟩
  obtain ⟨C, hzC, hCV, hCt, hC, hCi, hCz, hCS⟩ :=
    HamiltonIndexOne.exists_pair_chart_of_finitePL_plane_patch_at (by simp)
      hPL hinj hzLi hV (by simpa only [Function.comp_apply, hliftz] using hzV) hfullV
  simp only [Function.comp_apply, hliftz] at hzC hCz
  let H := G.trans C
  have hHt : H.target = C.target := by
    apply inter_eq_left.mpr
    intro x hx
    exact hVt (hCV (C.map_target hx))
  have hHU : H.source ⊆ U ∩ G.source := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (hCV hx.2).2
    exact ⟨G.injOn hy.2 hx.1 hyx ▸ hy.1, hx.1⟩
  refine ⟨H, ⟨hzG, hzC⟩, hHU, hHt.trans hCt, hCz, ?_, ?_⟩
  · intro x hx
    have hmem : x ∈ f '' K.space ↔ G x ∈ T := by
      constructor
      · intro hxS
        exact ⟨x, ⟨hxS, hx.1⟩, rfl⟩
      · rintro ⟨y, ⟨hyS, hyG⟩, hyx⟩
        exact G.injOn hyG hx.1 hyx ▸ hyS
    exact hmem.trans (hCS (G x) hx.2)
  · intro i
    have hc := (mem_piecewiseAffineGroupoid_iff V3 _).mp (hcompat i)
    have hforward : LocallyPiecewiseAffineOn (((e i).symm.trans G).trans C)
        (((e i).symm.trans G).trans C).source := hC.comp hc.1
    have hinverse : LocallyPiecewiseAffineOn (C.symm.trans (G.symm.trans (e i)))
        (C.symm.trans (G.symm.trans (e i))).source := hc.2.comp hCi
    constructor
    · simpa only [H, OpenPartialHomeomorph.trans_assoc] using hforward
    · simpa only [H, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hinverse

namespace ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)

theorem exists_embedded_interior_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ (V1 × V2)) (hK : K.faces.Finite)
    (hKs : K.space = source)
    {f : (V1 × V2) → X} (hf : PolyhedralPLInCharts e f K.space)
    (hemb : IsEmbedding (fun z : K.space ↦ f z))
    (G : OpenPartialHomeomorph X V3)
    (hcompat : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3)
    (z : K.space) (hzr : (z : V1 × V2).1 ∉ sphere (0 : V1) 1)
    (hzG : f z ∈ G.source) {U : Set X} (hU : IsOpen U) (hfzU : f z ∈ U) :
    ∃ H : OpenPartialHomeomorph X C3,
      f z ∈ H.source ∧ H.source ⊆ U ∩ G.source ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧ H (f z) = 0 ∧
      (∀ x ∈ H.source, x ∈ f '' K.space ↔ (H x).2 = 0) ∧
      ∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source := by
  let eK : K.space ≃ₜ source := Homeomorph.setCongr hKs
  obtain ⟨q₀, O, F, hzq, _, _, _, _, _, hqPL⟩ :=
    exists_interior_source_parameters (eK z) hzr
  let q := eK.toOpenPartialHomeomorph.trans q₀
  have hqt : q.target = q₀.target := by
    change q₀.target ∩ q₀.symm ⁻¹' (univ : Set source) = q₀.target
    rw [preimage_univ, inter_univ]
  have hq : LocallyPiecewiseAffineOn (fun u ↦ (q.symm u : V1 × V2)) q.target := by
    rw [hqt]
    exact hqPL
  exact exists_embedded_source_plane_chart K hK hf hemb G hcompat z hzG q
    ⟨mem_univ _, hzq⟩ hq hU hfzU

end ProtectedAnnulus

end PoincareConjecture.M76.Dehn
