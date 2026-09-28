import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.CarrierBallCertificates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalFiniteSphereCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalEndpointBallAttachment

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem polyhedralPLInCharts_of_finite_carrier_formula
    {E F α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {W : Set F}
    (atlas : α → OpenPartialHomeomorph W V3)
    (hcover : ∀ x, ∃ i, x ∈ (atlas i).source)
    (hrep : ∀ i, ∃ (B : Set F) (g : F → V3), FinitePiecewiseAffineOn g B ∧
      ∀ x ∈ (atlas i).source, (x : F) ∈ B ∧ atlas i x = g x)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (f : E → W) (g : E → F) (hg : FinitePiecewiseAffineOn g K.space)
    (hval : ∀ x ∈ K.space, (f x : F) = g x) :
    PolyhedralPLInCharts atlas f K.space := by
  have hfc : Continuous (fun x : K.space => f x) := by
    apply continuous_induced_rng.mpr
    convert hg.continuousOn.domRestrict using 1
    funext x
    exact hval x x.property
  refine ⟨continuousOn_iff_continuous_domRestrict.mpr hfc, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover (f x)
  obtain ⟨J, V, hJ, hJK, hV, hxV, hVJ, hJO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x
      ((atlas i).open_source.preimage hfc) hi
  have hmap : MapsTo f J.space (atlas i).source :=
    fun y hy => hJO (show (⟨y, hJK hy⟩ : K.space) ∈ Subtype.val ⁻¹' J.space from hy)
  obtain ⟨B, q, hq, hqval⟩ := hrep i
  refine ⟨i, J, V, hJ, hJK, hV, hxV, hVJ, hmap, ?_⟩
  have hgB : MapsTo g J.space B := by
    intro y hy
    rw [← hval y (hJK hy)]
    exact (hqval (f y) (hmap hy)).1
  apply (hq.comp (hg.restrict J hJ hJK) hgB).congr
  intro y hy
  change q (g y) = atlas i (f y)
  rw [(hqval (f y) (hmap hy)).2, hval y (hJK hy)]

theorem OriginalFiniteSphereCollar.exists_realized_endpoint_attachment
    {X F ι α : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R S O : Set X} {B : Bool → Set X}
    (C : OriginalFiniteSphereCollar e R S O B)
    (phi : X → F) (hphi : Continuous phi)
    (hphiPL : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphii : InjOn phi R) {D W A : Set F}
    (hRD : phi '' R ⊆ D) (hDW : D ⊆ W)
    (atlas : α → OpenPartialHomeomorph W V3)
    (hcover : ∀ x, ∃ i, x ∈ (atlas i).source)
    (hcompat : ∀ i j, (atlas i).symm.trans (atlas j) ∈ piecewiseAffineGroupoid V3)
    (hrep : ∀ i, ∃ (Q : Set F) (g : F → V3), FinitePiecewiseAffineOn g Q ∧
      ∀ x ∈ (atlas i).source, (x : F) ∈ Q ∧ atlas i x = g x)
    (side : Bool) (hA : IsFinitePLBallPair V3 A (phi '' B side))
    (hAD : A ⊆ D) (hcontact : A ∩ phi '' closure O = phi '' B side) :
    ∃ A' : Set W, A' ⊆ (Subtype.val : W → F) ⁻¹' D ∧
      Nonempty (ChartwisePLBall atlas A' ((Subtype.val : W → F) ⁻¹' (phi '' S))) ∧
      (Subtype.val : W → F) ⁻¹' A ⊆ interior A' ∧
      A' ⊆ (Subtype.val : W → F) ⁻¹' (A ∪ phi '' closure O) := by
  classical
  let E := C.parameters → ℝ × V3
  let scale : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (C.width • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hscale (z : E × ℝ) : scale z = (z.1, C.width * z.2) := rfl
  let P : Set (E × ℝ) := C.complex.space ×ˢ Icc (-1 : ℝ) 1
  have hmapstrip : MapsTo scale P (C.complex.space ×ˢ Icc (-C.width) C.width) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change -C.width ≤ C.width * z.2 ∧ C.width * z.2 ≤ C.width
    constructor <;> nlinarith [hz.2.1, hz.2.2, C.width_pos]
  have hstripfull : C.complex.space ×ˢ Icc (-C.width) C.width ⊆ P := by
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2, C.width_le]⟩
  have hcR (z : E × ℝ) (hz : z ∈ P) : C.map (scale z) ∈ R :=
    interior_subset (C.closedInterior (mem_image_of_mem C.map (hmapstrip hz)))
  obtain ⟨K, hK, hKP⟩ := C.complex.exists_finite_interval_product C.finite
    (by norm_num : (-1 : ℝ) < 1)
  have hraw : PolyhedralPLInCharts e (C.map ∘ scale) K.space :=
    C.pl.comp_finitePiecewiseAffineOn K hK
      ((K.affineOnFaces_affine scale).finitePiecewiseAffineOn hK)
      (fun z hz => hstripfull (hmapstrip (hKP.subset hz)))
  let q : E × ℝ → F := phi ∘ C.map ∘ scale
  have hq : FinitePiecewiseAffineOn q K.space :=
    hraw.finitePiecewiseAffineOn_comp K hK hphiPL
  obtain ⟨p, hp, _⟩ := hA.sdiff_nonempty
  let v : E × ℝ → W := fun z => if hz : q z ∈ W then ⟨q z, hz⟩ else ⟨p, hDW (hAD hp)⟩
  have hvval (z : E × ℝ) (hz : z ∈ P) : (v z : F) = q z := by
    have : q z ∈ W := hDW (hRD (mem_image_of_mem phi (hcR z hz)))
    simp only [v, dif_pos this]
  have hv : PolyhedralPLInCharts atlas v P := by
    change PolyhedralPLInCharts atlas v (C.complex.space ×ˢ Icc (-1 : ℝ) 1)
    rw [← hKP]
    exact polyhedralPLInCharts_of_finite_carrier_formula atlas hcover hrep K hK
      v q hq (fun z hz => hvval z (hKP.subset hz))
  have hvinj : InjOn v P := by
    intro z hz w hw heq
    have hqeq := congrArg Subtype.val heq
    rw [hvval z hz, hvval w hw] at hqeq
    have hc := hphii (hcR z hz) (hcR w hw) hqeq
    have hs : scale z = scale w := congrArg Subtype.val
      (C.embedding.injective (a₁ := ⟨scale z, hstripfull (hmapstrip hz)⟩)
        (a₂ := ⟨scale w, hstripfull (hmapstrip hw)⟩) hc)
    have hfst := congrArg Prod.fst hs
    have hsnd := congrArg Prod.snd hs
    exact Prod.ext hfst (mul_left_cancel₀ C.width_pos.ne' hsnd)
  let : CompactSpace P := isCompact_iff_compactSpace.mp
    ((C.complex.isCompact_space_of_finite C.finite).prod isCompact_Icc)
  let vHomeo : P ≃ₜ v '' P := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn v P hvinj) (hv.continuousOn.domRestrict.subtype_mk _)
  have hvemb : Topology.IsEmbedding (fun z : P => v z) :=
    Topology.IsEmbedding.subtypeVal.comp vHomeo.isEmbedding
  have hzero (x : C.complex.space) :
      (v ((x : E), 0) : F) = phi (C.parametrization x) := by
    rw [hvval _ ⟨x.property, by norm_num⟩]
    change phi (C.map ((x : E), C.width * 0)) = _
    rw [mul_zero, C.center]
  have hSR : S ⊆ R := by
    intro x hx
    have hz := hcR (((C.parametrization.symm ⟨x, hx⟩ : C.complex.space) : E), 0)
      ⟨(C.parametrization.symm ⟨x, hx⟩).property, by norm_num⟩
    simpa only [hscale, mul_zero, C.center, C.parametrization.apply_symm_apply] using hz
  let centerMap : C.complex.space → ((Subtype.val : W → F) ⁻¹' (phi '' S)) :=
    fun x => ⟨v ((x : E), 0), by rw [mem_preimage, hzero]; exact mem_image_of_mem phi (C.parametrization x).property⟩
  have hcenterBij : Function.Bijective centerMap := by
    constructor
    · intro x y hxy
      apply C.parametrization.injective
      apply Subtype.ext
      apply hphii (hSR (C.parametrization x).property) (hSR (C.parametrization y).property)
      have h := congrArg (fun z : ((Subtype.val : W → F) ⁻¹' (phi '' S)) =>
        ((z : W) : F)) hxy
      simpa only [centerMap, hzero] using h
    · intro y
      obtain ⟨x, hx, heq⟩ := y.property
      refine ⟨C.parametrization.symm ⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change (v ((C.parametrization.symm ⟨x,hx⟩ : C.complex.space), 0) : F) = (y : W)
      rw [hzero, C.parametrization.apply_symm_apply]
      exact heq
  have hcenterCont : Continuous centerMap := by
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    convert hphi.comp (continuous_subtype_val.comp C.parametrization.continuous) using 1
    funext x
    exact hzero x
  let : CompactSpace C.complex.space :=
    isCompact_iff_compactSpace.mp (C.complex.isCompact_space_of_finite C.finite)
  let HB : C.complex.space ≃ₜ ((Subtype.val : W → F) ⁻¹' (phi '' S)) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective centerMap hcenterBij) hcenterCont
  have hvcenter (x : C.complex.space) : v ((x : E), 0) = HB x := rfl
  have hlevel : v '' (C.complex.space ×ˢ {if side then (1 : ℝ) else -1}) =
      (Subtype.val : W → F) ⁻¹' (phi '' B side) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzp : z ∈ P := ⟨hz.1, by rw [hz.2]; cases side <;> norm_num⟩
      rw [mem_preimage, hvval z hzp, C.endpoint_eq]
      refine mem_image_of_mem phi (mem_image_of_mem C.map ⟨hz.1, ?_⟩)
      change C.width * z.2 = if side then C.width else -C.width
      rw [hz.2]
      cases side <;> simp
    · rintro ⟨x, hx, heq⟩
      rw [C.endpoint_eq] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      let u : E × ℝ := (z.1, if side then 1 else -1)
      have hup : u ∈ P := ⟨hz.1, by cases side <;> norm_num [u]⟩
      refine ⟨u, ⟨hz.1, rfl⟩, Subtype.ext ?_⟩
      rw [hvval u hup]
      change phi (C.map (scale u)) = y
      convert heq using 1
      congr 2
      refine Prod.ext ?_ ?_
      · rfl
      change C.width * (if side then 1 else -1) = z.2
      rw [hz.2]
      cases side <;> simp
  have hclosed (z : E × ℝ) (hz : z ∈ P) : (v z : F) ∈ phi '' closure O := by
    rw [hvval z hz, C.closed_eq]
    exact mem_image_of_mem phi (mem_image_of_mem C.map (hmapstrip hz))
  have hballAvoid : (Subtype.val : W → F) ⁻¹' A ⊆
      (Subtype.val : W → F) ⁻¹' D \ v '' (C.complex.space ×ˢ Ioo (-1 : ℝ) 1) := by
    intro y hy
    refine ⟨hAD hy, ?_⟩
    rintro ⟨z, hz, rfl⟩
    have hzp : z ∈ P := ⟨hz.1, ⟨hz.2.1.le, hz.2.2.le⟩⟩
    have hb := hcontact.subset ⟨hy, hclosed z hzp⟩
    have hb' : v z ∈ v '' (C.complex.space ×ˢ {if side then (1 : ℝ) else -1}) :=
      hlevel.symm.subset hb
    obtain ⟨w, hw, heq⟩ := hb'
    have hwp : w ∈ P := ⟨hw.1, by rw [hw.2]; cases side <;> norm_num⟩
    have hwz := hvinj hwp hzp heq
    have ht : z.2 = if side then (1 : ℝ) else -1 := hwz ▸ hw.2
    cases side <;> simp_all only [Bool.false_eq_true, ↓reduceIte] <;> linarith [hz.2.1, hz.2.2]
  obtain ⟨ball⟩ := exists_chartwisePLBall_in_carrier atlas hcover hrep hA (hAD.trans hDW)
  have ball' : ChartwisePLBall atlas ((Subtype.val : W → F) ⁻¹' A)
      (v '' (C.complex.space ×ˢ {if side then (1 : ℝ) else -1})) := hlevel.symm ▸ ball
  obtain ⟨hnew, hinterior, hnewD⟩ := ball'.attach_original_endpoint_half_strip
    hcover hcompat C.complex C.finite HB v hv hvemb hvcenter
    (by norm_num : (0 : ℝ) < 1) le_rfl side hballAvoid
    (by
      rintro _ ⟨z, hz, rfl⟩
      change (v z : F) ∈ D
      rw [hvval z hz]
      exact hRD (mem_image_of_mem phi (hcR z hz)))
  refine ⟨_, hnewD, hnew, hinterior, union_subset ?_ ?_⟩
  · exact fun _ hx => Or.inl hx
  · rintro _ ⟨z, hz, rfl⟩
    apply Or.inr
    apply hclosed
    refine ⟨hz.1, ?_⟩
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc] at hz ⊢ <;>
      constructor <;> linarith [hz.2.1, hz.2.2]

end PoincareConjecture.M76
