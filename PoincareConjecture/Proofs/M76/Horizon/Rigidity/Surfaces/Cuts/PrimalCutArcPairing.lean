import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutBoundaryArcs








set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}

namespace OriginalPrimalCutDiskData

variable (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)

noncomputable def bridgeLabelling : Fin 4 ≃ ResidualHalfBandIndex K P D :=
  A.gaps.bridgeOrder.trans (exteriorFourIndex K P D labels)

def residualSheetFlip : ResidualHalfBandIndex K P D ≃ ResidualHalfBandIndex K P D where
  toFun i := (i.1, i.2 + 1)
  invFun i := (i.1, i.2 + 1)
  left_inv := by rintro ⟨s,j⟩; fin_cases j <;> rfl
  right_inv := by rintro ⟨s,j⟩; fin_cases j <;> rfl

noncomputable def arcPairing : Fin 4 ≃ Fin 4 :=
  A.bridgeLabelling.trans (residualSheetFlip.trans A.bridgeLabelling.symm)

theorem arcPairing_label (i : Fin 4) :
    A.bridgeLabelling (A.arcPairing i) = residualSheetFlip (A.bridgeLabelling i) := by
  simp [arcPairing]

theorem arcPairing_involutive : Function.Involutive A.arcPairing := by
  intro i
  apply A.bridgeLabelling.injective
  rw [A.arcPairing_label,A.arcPairing_label]
  obtain ⟨s,j⟩ := A.bridgeLabelling i
  fin_cases j <;> simp [residualSheetFlip]

theorem arcPairing_ne (i : Fin 4) : A.arcPairing i ≠ i := by
  intro he
  have hh := A.arcPairing_label i
  rw [he] at hh
  have hj := congrArg Prod.snd hh
  change (A.bridgeLabelling i).2 = (A.bridgeLabelling i).2 + 1 at hj
  generalize (A.bridgeLabelling i).2 = j at hj
  fin_cases j <;> contradiction

theorem sourceMap_sectorCopy (i : Fin 4) (x : E) : (A.sourceMap K P D hD hcofaces hP labels) (A.sectorCopy i x) = x := rfl

theorem sourceMap_copied_spoke (i t : Fin 4) :
    (A.sourceMap K P D hD hcofaces hP labels) '' (A.sectorCopy i '' A.sectors.spoke t) = A.sectors.spoke t := by
  rw [← image_comp]
  exact image_id _

noncomputable def sourceBridge (i : Fin 4) : Set E :=
  residualBridge K (complementaryOriginalEdge K P hcofaces (A.bridgeLabelling i).1.val)
    ((A.bands (A.bridgeLabelling i).1).ends 0) ((A.bands (A.bridgeLabelling i).1).ends 1)

theorem sourceMap_boundaryBridge (i : Fin 4) :
    (A.sourceMap K P D hD hcofaces hP labels) '' A.boundaryBridge i = A.sourceBridge i := by
  change (A.sourceMap K P D hD hcofaces hP labels) '' (zeroSheet '' (separatedSheet A.exteriorHeight
    (A.bridgeLabelling i) '' A.sourceBridge i)) = _
  rw [← image_comp,← image_comp]
  exact image_id _

theorem sourceBridge_paired (i : Fin 4) : A.sourceBridge (A.arcPairing i) = A.sourceBridge i := by
  unfold sourceBridge
  rw [A.arcPairing_label]
  rfl

theorem source_bridge_endpoints (i : Fin 4) :
    ({(A.sourceMap K P D hD hcofaces hP labels) (A.bridgeBegin i),(A.sourceMap K P D hD hcofaces hP labels) (A.bridgeEnd i)} : Set E) =
      {primalEdgeMark K (complementaryOriginalEdge K P hcofaces (A.bridgeLabelling i).1.val)
        ((A.bands (A.bridgeLabelling i).1).ends 0),
       primalEdgeMark K (complementaryOriginalEdge K P hcofaces (A.bridgeLabelling i).1.val)
        ((A.bands (A.bridgeLabelling i).1).ends 1)} := by
  have h := congrArg (fun S => Prod.fst '' S) (A.gaps.bridge_endpoints i)
  simp only [image_pair] at h
  exact h

theorem source_bridge_endpoints_paired (i : Fin 4) :
    ({(A.sourceMap K P D hD hcofaces hP labels) (A.bridgeBegin (A.arcPairing i)),(A.sourceMap K P D hD hcofaces hP labels) (A.bridgeEnd (A.arcPairing i))} : Set E) =
      {(A.sourceMap K P D hD hcofaces hP labels) (A.bridgeBegin i),(A.sourceMap K P D hD hcofaces hP labels) (A.bridgeEnd i)} := by
  rw [A.source_bridge_endpoints,A.source_bridge_endpoints,A.arcPairing_label]
  rfl

noncomputable def sourceSpokeAt (x : E) : Set E :=
  {z | ∃ t : Fin 4, originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order t) = x ∧
    z ∈ A.sectors.spoke t}

theorem sourceSpokeAt_mark (t : Fin 4) :
    A.sourceSpokeAt (originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order t)) =
      A.sectors.spoke t := by
  ext z
  constructor
  · rintro ⟨u,hu,hz⟩
    have h := A.sectors.order.injective
      (originalExteriorMarks_injective K P D hcofaces A.bands labels hu)
    exact h ▸ hz
  · exact fun hz => ⟨t,rfl,hz⟩

private theorem copied_spoke_source_at_endpoint (i t : Fin 4) (ht : t = i ∨ t = i+1)
    (b : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))
    (hb : (A.sectorCopy i '' A.sectors.spoke t) ∩ A.boundaryBridgeUnion = {b}) :
    (A.sourceMap K P D hD hcofaces hP labels) '' (A.sectorCopy i '' A.sectors.spoke t) = A.sourceSpokeAt ((A.sourceMap K P D hD hcofaces hP labels) b) := by
  have he := singleton_injective ((A.copied_spoke_inter_bridges i t ht).symm.trans hb)
  rw [← he,A.sourceMap_sectorCopy,A.sourceSpokeAt_mark,A.sourceMap_copied_spoke]

theorem sourceMap_gapSpoke_left (i : Fin 4) :
    (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes i).left = A.sourceSpokeAt ((A.sourceMap K P D hD hcofaces hP labels) (A.bridgeEnd i)) := by
  rcases (A.gapSpokes i).selection with ⟨hL,hR⟩ | ⟨hL,hR⟩
  · rw [hL]
    exact A.copied_spoke_source_at_endpoint _ _ (Or.inl rfl) _
      (hL ▸ (A.gapSpokes i).left_bridges)
  · rw [hL]
    exact A.copied_spoke_source_at_endpoint _ _ (Or.inr rfl) _
      (hL ▸ (A.gapSpokes i).left_bridges)

theorem sourceMap_gapSpoke_right (i : Fin 4) :
    (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes i).right = A.sourceSpokeAt ((A.sourceMap K P D hD hcofaces hP labels) (A.bridgeBegin (i+1))) := by
  rcases (A.gapSpokes i).selection with ⟨hL,hR⟩ | ⟨hL,hR⟩
  · rw [hR]
    exact A.copied_spoke_source_at_endpoint _ _ (Or.inr rfl) _
      (hR ▸ (A.gapSpokes i).right_bridges)
  · rw [hR]
    exact A.copied_spoke_source_at_endpoint _ _ (Or.inl rfl) _
      (hR ▸ (A.gapSpokes i).right_bridges)

theorem sourceMap_longBoundaryArc (i : Fin 4) :
    (A.sourceMap K P D hD hcofaces hP labels) '' A.longBoundaryArc i =
      (A.sourceSpokeAt ((A.sourceMap K P D hD hcofaces hP labels) (A.bridgeBegin i)) ∪ A.sourceBridge i) ∪
        A.sourceSpokeAt ((A.sourceMap K P D hD hcofaces hP labels) (A.bridgeEnd i)) := by
  rw [longBoundaryArc,image_union,image_union,A.sourceMap_gapSpoke_right,
    A.sourceMap_gapSpoke_left,A.sourceMap_boundaryBridge,sub_add_cancel]

theorem sourceMap_longBoundaryArc_paired (i : Fin 4) :
    (A.sourceMap K P D hD hcofaces hP labels) '' A.longBoundaryArc (A.arcPairing i) = (A.sourceMap K P D hD hcofaces hP labels) '' A.longBoundaryArc i := by
  rw [A.sourceMap_longBoundaryArc,A.sourceMap_longBoundaryArc,A.sourceBridge_paired]
  rcases pair_eq_pair_iff.mp (A.source_bridge_endpoints_paired i) with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · rw [h0,h1]
  · rw [h0,h1]
    ac_rfl

omit [FiniteDimensional ℝ E] [DecidableEq E] in
private theorem affine_finitePL_on_ball {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s b : Set X} (hs : IsFinitePLBallPair ℝ s b) (f : X →ᴬ[ℝ] E) :
    FinitePiecewiseAffineOn f s := by
  obtain ⟨_,c,_,_,_,e,⟨g,⟨J,hJ,hJs,_⟩,_⟩,_⟩ := hs
  exact ⟨J,hJ,hJs,J.affineOnFaces_affine f⟩

omit [DecidableEq E] in
private theorem projection_piece_homeomorph {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {s t : Set X} {f : X → E}
    (hs : FinitePiecewiseAffineOn f s) (ht : FinitePiecewiseAffineOn f t)
    (hsi : InjOn f s) (hti : InjOn f t) (himage : f '' s = f '' t) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧ ∀ x : s, f (H x) = f x := by
  obtain ⟨e,he,heval⟩ := hs.exists_homeomorph_image hsi
  obtain ⟨d,hd,hdval⟩ := ht.exists_homeomorph_image hti
  obtain ⟨g,⟨J,hJ,hJs,_⟩,_⟩ := he.symm
  let H := (e.trans (Homeomorph.setCongr himage)).trans d.symm
  refine ⟨H,(he.trans (Homeomorph.isFinitePL_setCongr himage J hJ hJs)).trans hd.symm,?_⟩
  intro x
  have h := hdval (H x)
  have h' : (d (H x) : E) = (e x : E) := by
    change (d (d.symm ((Homeomorph.setCongr himage) (e x))) : E) = _
    rw [d.apply_symm_apply]
    rfl
  exact h.symm.trans (h'.trans (heval x))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E] in
private theorem source_preserving_union {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {s u t v : Set X} {f : X → E} {p q : X}
    (e : s ≃ₜ t) (d : u ≃ₜ v) (he : e.IsFinitePL) (hd : d.IsFinitePL)
    (hep : ∀ x : s, f (e x) = f x) (hdp : ∀ x : u, f (d x) = f x)
    (hinter : s ∩ u = {p}) (hinter' : t ∩ v = {q})
    (heq : ∀ hp : p ∈ s, (e ⟨p,hp⟩ : X) = q)
    (hdq : ∀ hp : p ∈ u, (d ⟨p,hp⟩ : X) = q) :
    ∃ H : (s ∪ u : Set X) ≃ₜ (t ∪ v : Set X), H.IsFinitePL ∧
      (∀ x : s, (H ⟨x,Or.inl x.property⟩ : X) = e x) ∧
      (∀ x : u, (H ⟨x,Or.inr x.property⟩ : X) = d x) ∧
      ∀ x : (s ∪ u : Set X), f (H x) = f x := by
  have hp := hinter.symm.subset (mem_singleton p)
  have hq := hinter'.symm.subset (mem_singleton q)
  have hoverlap (x : s) : (x : X) ∈ u ↔ (e x : X) ∈ v := by
    constructor
    · intro hx
      have hext : (x : X) = p := hinter.subset ⟨x.property,hx⟩
      have hxe : x = ⟨p,hp.1⟩ := Subtype.ext hext
      rw [hxe,heq hp.1]
      exact hq.2
    · intro hx
      have hext : (e x : X) = q := hinter'.subset ⟨(e x).property,hx⟩
      have hxe : e x = e ⟨p,hp.1⟩ := Subtype.ext (hext.trans (heq hp.1).symm)
      have hxp : x = ⟨p,hp.1⟩ := e.injective hxe
      rw [hxp]
      exact hp.2
  have hagree (x : X) (hxs : x ∈ s) (hxu : x ∈ u) :
      (e ⟨x,hxs⟩ : X) = (d ⟨x,hxu⟩ : X) := by
    have hext : x = p := hinter.subset ⟨hxs,hxu⟩
    subst x
    exact (heq hxs).trans (hdq hxu).symm
  obtain ⟨H,hH,hHs,hHu⟩ := Homeomorph.exists_union_finitePL e d he hd hoverlap hagree
  refine ⟨H,hH,hHs,hHu,?_⟩
  intro x
  rcases x.property with hx | hx
  · exact (congrArg f (hHs ⟨x,hx⟩)).trans (hep ⟨x,hx⟩)
  · exact (congrArg f (hHu ⟨x,hx⟩)).trans (hdp ⟨x,hx⟩)

omit [DecidableEq E] in
private theorem three_piece_projection_homeomorph {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {s₀ s₁ s₂ t₀ t₁ t₂ : Set X} {f : X → E} {p₀ p₁ q₀ q₁ : X}
    (hs₀ : FinitePiecewiseAffineOn f s₀) (hs₁ : FinitePiecewiseAffineOn f s₁)
    (hs₂ : FinitePiecewiseAffineOn f s₂) (ht₀ : FinitePiecewiseAffineOn f t₀)
    (ht₁ : FinitePiecewiseAffineOn f t₁) (ht₂ : FinitePiecewiseAffineOn f t₂)
    (his₀ : InjOn f s₀) (his₁ : InjOn f s₁) (his₂ : InjOn f s₂)
    (hit₀ : InjOn f t₀) (hit₁ : InjOn f t₁) (hit₂ : InjOn f t₂)
    (hi₀ : f '' s₀ = f '' t₀) (hi₁ : f '' s₁ = f '' t₁) (hi₂ : f '' s₂ = f '' t₂)
    (hc₀ : s₀ ∩ s₁ = {p₀}) (hc₁ : s₁ ∩ s₂ = {p₁}) (hsdis : Disjoint s₀ s₂)
    (hd₀ : t₀ ∩ t₁ = {q₀}) (hd₁ : t₁ ∩ t₂ = {q₁}) (htdis : Disjoint t₀ t₂)
    (hpt₀ : f p₀ = f q₀) (hpt₁ : f p₁ = f q₁) :
    ∃ H : ((s₀∪s₁)∪s₂ : Set X) ≃ₜ ((t₀∪t₁)∪t₂ : Set X), H.IsFinitePL ∧
      (∀ x, f (H x) = f x) ∧
      (∀ x : s₀, (H ⟨x,Or.inl (Or.inl x.property)⟩ : X) ∈ t₀) ∧
      (∀ x : s₂, (H ⟨x,Or.inr x.property⟩ : X) ∈ t₂) := by
  obtain ⟨e₀,he₀,hv₀⟩ := projection_piece_homeomorph hs₀ ht₀ his₀ hit₀ hi₀
  obtain ⟨e₁,he₁,hv₁⟩ := projection_piece_homeomorph hs₁ ht₁ his₁ hit₁ hi₁
  obtain ⟨e₂,he₂,hv₂⟩ := projection_piece_homeomorph hs₂ ht₂ his₂ hit₂ hi₂
  have hp₀ := hc₀.symm.subset (mem_singleton p₀)
  have hp₁ := hc₁.symm.subset (mem_singleton p₁)
  have hq₀ := hd₀.symm.subset (mem_singleton q₀)
  have hq₁ := hd₁.symm.subset (mem_singleton q₁)
  have he₀q : ∀ hp : p₀ ∈ s₀, (e₀ ⟨p₀,hp⟩ : X) = q₀ := fun hp =>
    hit₀ (e₀ ⟨p₀,hp⟩).property hq₀.1 ((hv₀ ⟨p₀,hp⟩).trans hpt₀)
  have he₁q : ∀ hp : p₀ ∈ s₁, (e₁ ⟨p₀,hp⟩ : X) = q₀ := fun hp =>
    hit₁ (e₁ ⟨p₀,hp⟩).property hq₀.2 ((hv₁ ⟨p₀,hp⟩).trans hpt₀)
  obtain ⟨H,hH,hH₀,hH₁,hHv⟩ := source_preserving_union e₀ e₁ he₀ he₁ hv₀ hv₁ hc₀ hd₀ he₀q he₁q
  have hc : (s₀∪s₁)∩s₂ = {p₁} := by
    rw [union_inter_distrib_right,disjoint_iff_inter_eq_empty.mp hsdis,empty_union,hc₁]
  have hd : (t₀∪t₁)∩t₂ = {q₁} := by
    rw [union_inter_distrib_right,disjoint_iff_inter_eq_empty.mp htdis,empty_union,hd₁]
  have hHq : ∀ hp : p₁ ∈ s₀∪s₁, (H ⟨p₁,hp⟩ : X) = q₁ := by
    intro hp
    have h := hH₁ ⟨p₁,hp₁.1⟩
    exact h.trans (hit₁ (e₁ ⟨p₁,hp₁.1⟩).property hq₁.1 ((hv₁ ⟨p₁,hp₁.1⟩).trans hpt₁))
  have he₂q : ∀ hp : p₁ ∈ s₂, (e₂ ⟨p₁,hp⟩ : X) = q₁ := fun hp =>
    hit₂ (e₂ ⟨p₁,hp⟩).property hq₁.2 ((hv₂ ⟨p₁,hp⟩).trans hpt₁)
  obtain ⟨G,hG,hG₀,hG₂,hGv⟩ := source_preserving_union H e₂ hH he₂ hHv hv₂ hc hd hHq he₂q
  refine ⟨G,hG,hGv,?_,?_⟩
  · intro x
    rw [hG₀ ⟨x,Or.inl x.property⟩,hH₀ x]
    exact (e₀ x).property
  · intro x
    rw [hG₂ x]
    exact (e₂ x).property

theorem sourceMap_injOn_copied_spoke (i t : Fin 4) :
    InjOn (A.sourceMap K P D hD hcofaces hP labels) (A.sectorCopy i '' A.sectors.spoke t) := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ he
  exact congrArg (A.sectorCopy i) he

theorem sourceMap_injOn_gapSpoke_left (i : Fin 4) :
    InjOn (A.sourceMap K P D hD hcofaces hP labels) (A.gapSpokes i).left := by
  rcases (A.gapSpokes i).selection with ⟨hL,_⟩ | ⟨hL,_⟩ <;>
    rw [hL] <;> exact A.sourceMap_injOn_copied_spoke _ _

theorem sourceMap_injOn_gapSpoke_right (i : Fin 4) :
    InjOn (A.sourceMap K P D hD hcofaces hP labels) (A.gapSpokes i).right := by
  rcases (A.gapSpokes i).selection with ⟨_,hR⟩ | ⟨_,hR⟩ <;>
    rw [hR] <;> exact A.sourceMap_injOn_copied_spoke _ _

theorem sourceMap_injOn_boundaryBridge (i : Fin 4) :
    InjOn (A.sourceMap K P D hD hcofaces hP labels) (A.boundaryBridge i) := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩ _ ⟨_,⟨y,hy,rfl⟩,rfl⟩ he
  exact congrArg (fun x => zeroSheet (ι := Fin 4)
    (separatedSheet A.exteriorHeight (A.bridgeLabelling i) x)) he

private theorem sourceMap_finitePL_on_interval
    {s b : Set ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))}
    (hs : IsFinitePLBallPair ℝ s b) :
    FinitePiecewiseAffineOn (A.sourceMap K P D hD hcofaces hP labels) s :=
  affine_finitePL_on_ball hs
    (((ContinuousLinearMap.fst ℝ E (ResidualHalfBandIndex K P D → ℝ)).comp
      (ContinuousLinearMap.fst ℝ (E × (ResidualHalfBandIndex K P D → ℝ)) (Fin 4 → ℝ))).toContinuousAffineMap)

theorem gapSpoke_right_bridge_inter (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4) :
    (A.gapSpokes (i-1)).right ∩ A.boundaryBridge i = {A.bridgeBegin i} := by
  ext x
  rw [A.gapSpoke_right_bridge_contact hbound,sub_add_cancel]
  simp

theorem bridge_gapSpoke_left_inter (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4) :
    A.boundaryBridge i ∩ (A.gapSpokes i).left = {A.bridgeEnd i} := by
  rw [inter_comm]
  ext x
  rw [A.gapSpoke_left_bridge_contact hbound]
  simp

theorem longBoundaryArc_endSpokes_disjoint (i : Fin 4) :
    Disjoint (A.gapSpokes (i-1)).right (A.gapSpokes i).left :=
  (A.gapSpokes_different_disjoint (by fin_cases i <;> decide)).mono
    subset_union_right subset_union_left

noncomputable def arcStart (i : Fin 4) : A.longBoundaryArc i :=
  ⟨A.gapCenter (i-1),Or.inl (Or.inl ((A.gapSpokes (i-1)).right_ball.1 (Or.inl rfl)))⟩

noncomputable def arcFinish (i : Fin 4) : A.longBoundaryArc i :=
  ⟨A.gapCenter i,Or.inr ((A.gapSpokes i).left_ball.1 (Or.inl rfl))⟩



theorem exists_longBoundaryArc_pairing_homeomorph_with_endpoints
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4) :
    ∃ H : A.longBoundaryArc i ≃ₜ A.longBoundaryArc (A.arcPairing i), H.IsFinitePL ∧
      (∀ x, A.sourceMap K P D hD hcofaces hP labels (H x) =
        A.sourceMap K P D hD hcofaces hP labels x) ∧
      ((A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin (A.arcPairing i)) =
          A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin i) ∧
        H (A.arcStart i) = A.arcStart (A.arcPairing i) ∧
        H (A.arcFinish i) = A.arcFinish (A.arcPairing i)) ∨
       (A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin (A.arcPairing i)) =
          A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i) ∧
        H (A.arcStart i) = A.arcFinish (A.arcPairing i) ∧
        H (A.arcFinish i) = A.arcStart (A.arcPairing i))) := by
  let j := A.arcPairing i
  have hR (k : Fin 4) := A.sourceMap_finitePL_on_interval (A.gapSpokes (k-1)).right_ball
  have hL (k : Fin 4) := A.sourceMap_finitePL_on_interval (A.gapSpokes k).left_ball
  have hB (k : Fin 4) := A.sourceMap_finitePL_on_interval (A.boundaryBridge_interval k)
  have hBR : (A.sourceMap K P D hD hcofaces hP labels) '' A.boundaryBridge i =
      (A.sourceMap K P D hD hcofaces hP labels) '' A.boundaryBridge j := by
    rw [A.sourceMap_boundaryBridge,A.sourceMap_boundaryBridge,A.sourceBridge_paired]
  rcases pair_eq_pair_iff.mp (A.source_bridge_endpoints_paired i) with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · have hRR : (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes (i-1)).right =
        (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes (j-1)).right := by
      rw [A.sourceMap_gapSpoke_right,A.sourceMap_gapSpoke_right,sub_add_cancel,sub_add_cancel,h0]
    have hLL : (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes i).left =
        (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes j).left := by
      rw [A.sourceMap_gapSpoke_left,A.sourceMap_gapSpoke_left,h1]
    obtain ⟨H,hH,hHv,hH0,hH2⟩ := three_piece_projection_homeomorph (hR i) (hB i) (hL i) (hR j) (hB j) (hL j)
      (A.sourceMap_injOn_gapSpoke_right _) (A.sourceMap_injOn_boundaryBridge _)
      (A.sourceMap_injOn_gapSpoke_left _) (A.sourceMap_injOn_gapSpoke_right _)
      (A.sourceMap_injOn_boundaryBridge _) (A.sourceMap_injOn_gapSpoke_left _) hRR hBR hLL
      (A.gapSpoke_right_bridge_inter hbound i) (A.bridge_gapSpoke_left_inter hbound i)
      (A.longBoundaryArc_endSpokes_disjoint i)
      (A.gapSpoke_right_bridge_inter hbound j) (A.bridge_gapSpoke_left_inter hbound j)
      (A.longBoundaryArc_endSpokes_disjoint j) h0.symm h1.symm
    refine ⟨H,hH,hHv,Or.inl ⟨h0,?_,?_⟩⟩
    · apply Subtype.ext
      exact A.sourceMap_injOn_gapSpoke_right (j-1)
        (hH0 ⟨A.gapCenter (i-1),(A.gapSpokes (i-1)).right_ball.1 (Or.inl rfl)⟩)
        ((A.gapSpokes (j-1)).right_ball.1 (Or.inl rfl)) (hHv (A.arcStart i))
    · apply Subtype.ext
      exact A.sourceMap_injOn_gapSpoke_left j
        (hH2 ⟨A.gapCenter i,(A.gapSpokes i).left_ball.1 (Or.inl rfl)⟩)
        ((A.gapSpokes j).left_ball.1 (Or.inl rfl)) (hHv (A.arcFinish i))
  · have hRL : (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes (i-1)).right =
        (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes j).left := by
      rw [A.sourceMap_gapSpoke_right,A.sourceMap_gapSpoke_left,sub_add_cancel,h1]
    have hLR : (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes i).left =
        (A.sourceMap K P D hD hcofaces hP labels) '' (A.gapSpokes (j-1)).right := by
      rw [A.sourceMap_gapSpoke_left,A.sourceMap_gapSpoke_right,sub_add_cancel,h0]
    have hc0 : (A.gapSpokes j).left ∩ A.boundaryBridge j = {A.bridgeEnd j} := by
      rw [inter_comm,A.bridge_gapSpoke_left_inter hbound]
    have hc1 : A.boundaryBridge j ∩ (A.gapSpokes (j-1)).right = {A.bridgeBegin j} := by
      rw [inter_comm,A.gapSpoke_right_bridge_inter hbound]
    obtain ⟨H,hH,hHv,hH0,hH2⟩ := three_piece_projection_homeomorph (hR i) (hB i) (hL i) (hL j) (hB j) (hR j)
      (A.sourceMap_injOn_gapSpoke_right _) (A.sourceMap_injOn_boundaryBridge _)
      (A.sourceMap_injOn_gapSpoke_left _) (A.sourceMap_injOn_gapSpoke_left _)
      (A.sourceMap_injOn_boundaryBridge _) (A.sourceMap_injOn_gapSpoke_right _) hRL hBR hLR
      (A.gapSpoke_right_bridge_inter hbound i) (A.bridge_gapSpoke_left_inter hbound i)
      (A.longBoundaryArc_endSpokes_disjoint i) hc0 hc1
      (A.longBoundaryArc_endSpokes_disjoint j).symm h1.symm h0.symm
    have hrev : ((A.gapSpokes j).left ∪ A.boundaryBridge j) ∪ (A.gapSpokes (j-1)).right =
        A.longBoundaryArc j := by unfold longBoundaryArc; ac_rfl
    let G := H.trans (Homeomorph.setCongr hrev)
    obtain ⟨f,⟨J,hJ,hJs,_⟩,_⟩ := hH.symm
    have hG : G.IsFinitePL := hH.trans (Homeomorph.isFinitePL_setCongr hrev J hJ hJs)
    refine ⟨G,hG,hHv,Or.inr ⟨h0,?_,?_⟩⟩
    · apply Subtype.ext
      exact A.sourceMap_injOn_gapSpoke_left j
        (hH0 ⟨A.gapCenter (i-1),(A.gapSpokes (i-1)).right_ball.1 (Or.inl rfl)⟩)
        ((A.gapSpokes j).left_ball.1 (Or.inl rfl)) (hHv (A.arcStart i))
    · apply Subtype.ext
      exact A.sourceMap_injOn_gapSpoke_right (j-1)
        (hH2 ⟨A.gapCenter i,(A.gapSpokes i).left_ball.1 (Or.inl rfl)⟩)
        ((A.gapSpokes (j-1)).right_ball.1 (Or.inl rfl)) (hHv (A.arcFinish i))

theorem exists_longBoundaryArc_pairing_homeomorph
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4) :
    ∃ H : A.longBoundaryArc i ≃ₜ A.longBoundaryArc (A.arcPairing i), H.IsFinitePL ∧
      ∀ x, A.sourceMap K P D hD hcofaces hP labels (H x) =
        A.sourceMap K P D hD hcofaces hP labels x := by
  obtain ⟨H,hH,hv,_⟩ := A.exists_longBoundaryArc_pairing_homeomorph_with_endpoints hbound i
  exact ⟨H,hH,hv⟩

theorem copied_spoke_contact_endpoint (i t : Fin 4) (ht : t = i ∨ t = i+1)
    (b : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))
    (hb : (A.sectorCopy i '' A.sectors.spoke t) ∩ A.boundaryBridgeUnion = {b}) :
    A.sectorCopy i (originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order t)) = b :=
  singleton_injective ((A.copied_spoke_inter_bridges i t ht).symm.trans hb)




theorem exists_gapSpoke_original_indices (i : Fin 4) :
    ∃ l r : Fin 4, ({l,r} : Set (Fin 4)) = {A.matching i,A.matching i+1} ∧
      (A.gapSpokes i).left = A.sectorCopy (A.matching i) '' A.sectors.spoke l ∧
      (A.gapSpokes i).right = A.sectorCopy (A.matching i) '' A.sectors.spoke r ∧
      originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order l) =
        A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i) ∧
      originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order r) =
        A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin (i+1)) := by
  rcases (A.gapSpokes i).selection with ⟨hL,hR⟩ | ⟨hL,hR⟩
  · refine ⟨A.matching i,A.matching i+1,rfl,hL,hR,?_,?_⟩
    · exact congrArg (A.sourceMap K P D hD hcofaces hP labels)
        (A.copied_spoke_contact_endpoint _ _ (Or.inl rfl) _
          (hL ▸ (A.gapSpokes i).left_bridges))
    · exact congrArg (A.sourceMap K P D hD hcofaces hP labels)
        (A.copied_spoke_contact_endpoint _ _ (Or.inr rfl) _
          (hR ▸ (A.gapSpokes i).right_bridges))
  · refine ⟨A.matching i+1,A.matching i,Set.pair_comm _ _,hL,hR,?_,?_⟩
    · exact congrArg (A.sourceMap K P D hD hcofaces hP labels)
        (A.copied_spoke_contact_endpoint _ _ (Or.inr rfl) _
          (hL ▸ (A.gapSpokes i).left_bridges))
    · exact congrArg (A.sourceMap K P D hD hcofaces hP labels)
        (A.copied_spoke_contact_endpoint _ _ (Or.inl rfl) _
          (hR ▸ (A.gapSpokes i).right_bridges))

end OriginalPrimalCutDiskData
end PoincareConjecture.M76.OriginalTriangleCopies
