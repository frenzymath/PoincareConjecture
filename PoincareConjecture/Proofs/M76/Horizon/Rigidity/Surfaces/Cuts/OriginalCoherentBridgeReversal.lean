import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalRefinementCoherentSigns
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBridgeCofaceGerms
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBridgeEdgeCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBridgeScalarDirections
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBridgeScalarCharts



set_option autoImplicit false

open Set Geometry Classical AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem scalar_product_neg_of_parity
    (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hp : orientationSignParity (SignType.sign r) +
      orientationSignParity (SignType.sign s) = 1) : r * s < 0 := by
  rcases lt_or_gt_of_ne hr with hr | hr <;> rcases lt_or_gt_of_ne hs with hs | hs
  · rw [sign_neg hr, sign_neg hs] at hp
    norm_num [orientationSignParity] at hp
    exact (show (2 : ZMod 2) ≠ 1 by decide) hp |>.elim
  · exact mul_neg_of_neg_of_pos hr hs
  · exact mul_neg_of_pos_of_neg hr hs
  · rw [sign_pos hr, sign_pos hs] at hp
    norm_num [orientationSignParity] at hp

omit [FiniteDimensional ℝ E] in


theorem OriginalRefinementCoherentSigns.paired_edge_scalar_product_neg
    {K : SimplicialComplex ℝ E} {number : E → ℕ} {sourceSign : Finset E → ZMod 2}
    {L : SimplicialComplex ℝ (ℝ × ℝ)} {refinedNumber : (ℝ × ℝ) → ℕ}
    {F : (ℝ × ℝ) → E}
    (O : OriginalRefinementCoherentSigns K number sourceSign L refinedNumber F)
    (t u : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3})
    (p q : Fin 3 → ℝ × ℝ) (hp : ∀ j, p j ∈ t.val) (hq : ∀ j, q j ∈ u.val)
    (hpi : Function.Injective p) (hqi : Function.Injective q)
    (v w : E) (hvw : v ≠ w)
    (hvwt : {v, w} ⊆ (O.owner t).val) (hvwu : {v, w} ⊆ (O.owner u).val)
    (hcancel :
      (sourceSign (O.owner t).val + boundaryFaceParity number (O.owner t).val {v, w}) +
        (sourceSign (O.owner u).val + boundaryFaceParity number (O.owner u).val {v, w}) = 1)
    (hboundary : O.sign t + Dehn.orderedCofaceParity refinedNumber t.val (p 0) (p 1) =
      O.sign u + Dehn.orderedCofaceParity refinedNumber u.val (q 0) (q 1))
    (r₀ r₁ s₀ s₁ : ℝ)
    (hpr₀ : F (p 0) - v = r₀ • (w - v)) (hpr₁ : F (p 1) - v = r₁ • (w - v))
    (hqs₀ : F (q 0) - v = s₀ • (w - v)) (hqs₁ : F (q 1) - v = s₁ • (w - v)) :
    (r₁ - r₀) * (s₁ - s₀) < 0 := by
  obtain ⟨c, hc, hct⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hvwt, by simp [hvw, (O.owner t).property.2]⟩
  obtain ⟨d, hd, hdu⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hvwu, by simp [hvw, (O.owner u).property.2]⟩
  have hcne : c ≠ v ∧ c ≠ w := by simpa using hc
  have hdne : d ≠ v ∧ d ≠ w := by simpa using hd
  have ht : (O.owner t).val = {v, w, c} := by
    rw [← hct]
    ext z
    simp [or_comm, or_left_comm]
  have hu : (O.owner u).val = {v, w, d} := by
    rw [← hdu]
    ext z
    simp [or_comm, or_left_comm]
  have hrt := O.signed_edge_scalar_parity t (p 0) (p 1) (p 2) (hp 0) (hp 1) (hp 2)
    (hpi.ne (by decide)) (hpi.ne (by decide)) (hpi.ne (by decide))
    v w c ht hvw hcne.1.symm hcne.2.symm r₀ r₁ hpr₀ hpr₁
  have hsu := O.signed_edge_scalar_parity u (q 0) (q 1) (q 2) (hq 0) (hq 1) (hq 2)
    (hqi.ne (by decide)) (hqi.ne (by decide)) (hqi.ne (by decide))
    v w d hu hvw hdne.1.symm hdne.2.symm s₀ s₁ hqs₀ hqs₁
  have hc := Dehn.orderedCofaceParity_cancellation number (O.owner t).val (O.owner u).val
    v w (sourceSign (O.owner t).val) (sourceSign (O.owner u).val) hcancel
  apply scalar_product_neg_of_parity _ _ hrt.1 hsu.1
  linear_combination (norm := ring_nf) hc + hboundary - hrt.2 - hsu.2
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero, sub_zero]

end PoincareConjecture.M76.OriginalTriangleCopies

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

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
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)

local notation "CutSpace" => (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)
local notation "sm" => A.sourceMap K P D hD hcofaces hP labels
local notation "Sq" => PeriodicSquare.squareCarrier 1



theorem exists_refined_bridge_edge_sample
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (hL : L.faces.Finite) (hLs : L.space = Sq)
    (f : (ℝ × ℝ) → CutSpace) (hf : L.AffineOnFaces f)
    (hF : L.AffineOnFaces (sm ∘ f)) (hmap : MapsTo f L.space A.carrier)
    (hfaces : ∀ t ∈ L.faces, InjOn (sm ∘ f) (convexHull ℝ (t : Set (ℝ × ℝ))))
    {number : E → ℕ} {sourceSign : Finset E → ZMod 2} {refinedNumber : (ℝ × ℝ) → ℕ}
    (O : OriginalRefinementCoherentSigns K number sourceSign L refinedNumber (sm ∘ f))
    (i : Fin 4) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (hbridge : ∀ q ∈ Ioo α β,
      f (unitSquareSide i q) ∈ A.boundaryBridge i \ {A.bridgeBegin i, A.bridgeEnd i}) :
    ∃ (q r s : ℝ) (t : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3}),
      q ∈ Ioo α β ∧ q ∈ Ioo r s ∧ r < s ∧
      {unitSquareSide i r, unitSquareSide i s} ∈ (L.frontierSubcomplex L.space).faces ∧
      {unitSquareSide i r, unitSquareSide i s} ⊆ t.val ∧
      (O.owner t).val =
        ((A.bands (A.bridgeLabelling i).1).coface (A.bridgeLabelling i).2).val ∧
      sm (f (unitSquareSide i r)) ∈ segment ℝ
        ((A.bands (A.bridgeLabelling i).1).ends 0).val
        ((A.bands (A.bridgeLabelling i).1).ends 1).val ∧
      sm (f (unitSquareSide i s)) ∈ segment ℝ
        ((A.bands (A.bridgeLabelling i).1).ends 0).val
        ((A.bands (A.bridgeLabelling i).1).ends 1).val := by
  have hbad : ((unitSquareSide i) ⁻¹' L.vertices).Finite :=
    (L.finite_vertices_of_finite_faces hL).preimage (unitSquareSide_injective i).injOn
  obtain ⟨q, hq, hqv⟩ := ((Set.Ioo_infinite hαβ).sdiff hbad).nonempty
  have hq01 : q ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hqfront : unitSquareSide i q ∈ frontier L.space :=
    hLs.symm ▸ unitSquareSide_mem_frontier i hq01
  obtain ⟨r, s, t, _, _, hrs, he, hqt, ht, htc, het⟩ :=
    exists_ordered_square_sample_edge L hL hLs hqfront hqv i q rfl
  let t' : {t : Finset (ℝ × ℝ) // t ∈ L.faces ∧ t.card = 3} := ⟨t, ht, htc⟩
  have hqhull : unitSquareSide i q ∈ convexHull ℝ (t : Set (ℝ × ℝ)) :=
    (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (het (by simp))) (subset_convexHull ℝ _ (het (by simp)))
      (openSegment_subset_segment ℝ _ _ hqt)
  have ho := A.refined_owner_at_boundaryBridge hpure L f hf hmap ht htc (hfaces t ht)
    (O.owner t').property.1 (O.owner t').property.2 (O.owner_mapsTo t') hqhull i
    (hbridge q hq).1 (fun h ↦ (hbridge q hq).2 (Or.inl h))
    (fun h ↦ (hbridge q hq).2 (Or.inr h))
  let B := A.bands (A.bridgeLabelling i).1
  let v : E := (B.ends 0).val
  let w : E := (B.ends 1).val
  have heT : ({v, w} : Finset E) ⊆ (O.owner t').val := by
    rw [ho]
    simpa [v, w, B.edge_eq] using B.edge_subset (A.bridgeLabelling i).2
  have hqbridge : sm (f (unitSquareSide i q)) ∈ A.sourceBridge i :=
    (A.sourceMap_boundaryBridge i).subset (mem_image_of_mem _ (hbridge q hq).1)
  have hqe : sm (f (unitSquareSide i q)) ∈ convexHull ℝ (({v, w} : Finset E) : Set E) := by
    have h := openSegment_subset_segment ℝ v w
      (residualBridge_subset_openEdge K _ B.edge_eq hqbridge)
    simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using h
  have hend := refined_boundary_edge_endpoints_in_original_face K L (sm ∘ f) hF ht
    (O.owner t').property.1 heT (O.owner_mapsTo t')
    (het (by simp)) (het (by simp)) hqt hqe
  refine ⟨q, r, s, t', hq, (unitSquareSide_mem_openSegment_iff i q r s hrs).mp hqt,
    hrs, he, het, ho, ?_, ?_⟩
  · simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair,
      Function.comp_apply, v, w, B] using hend.1
  · simpa only [Finset.coe_insert, Finset.coe_singleton, convexHull_pair,
      Function.comp_apply, v, w, B] using hend.2




theorem bridge_endpoint_scalar_parity
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (C : Sq ≃ₜ A.carrier) (f : (ℝ × ℝ) → CutSpace)
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (hL : L.faces.Finite) (hLs : L.space = Sq)
    (hf : L.AffineOnFaces f) (hF : L.AffineOnFaces (sm ∘ f))
    (hfaces : ∀ t ∈ L.faces, InjOn (sm ∘ f) (convexHull ℝ (t : Set (ℝ × ℝ))))
    (hval : ∀ x : Sq, f x.val = (C x).val)
    (hmark : ∀ (i : Fin 4) (x : Sq), (C x).val ∈ A.longBoundaryArc i ↔
      ![x.val.2 = 0, x.val.1 = 1, x.val.2 = 1, x.val.1 = 0] i)
    {number : E → ℕ} {sourceSign : Finset E → ZMod 2} {refinedNumber : (ℝ × ℝ) → ℕ}
    (O : OriginalRefinementCoherentSigns K number sourceSign L refinedNumber (sm ∘ f))
    (eps : ZMod 2)
    (hsign : ∀ t i r s,
      {unitSquareSide i r, unitSquareSide i s} ∈ (L.frontierSubcomplex L.space).faces →
      {unitSquareSide i r, unitSquareSide i s} ⊆ t.val → r < s →
      O.sign t + Dehn.orderedCofaceParity refinedNumber t.val
        (unitSquareSide i r) (unitSquareSide i s) = eps)
    (i : Fin 4) (ell : E →L[ℝ] ℝ)
    (hell : ell (((A.bands (A.bridgeLabelling i).1).ends 1).val -
      ((A.bands (A.bridgeLabelling i).1).ends 0).val) = 1)
    (helli : InjOn ell (range (AffineMap.lineMap
      ((A.bands (A.bridgeLabelling i).1).ends 0).val
      ((A.bands (A.bridgeLabelling i).1).ends 1).val : ℝ → E))) :
    ell (sm (A.bridgeEnd i)) - ell (sm (A.bridgeBegin i)) ≠ 0 ∧
      (sourceSign ((A.bands (A.bridgeLabelling i).1).coface (A.bridgeLabelling i).2).val +
        Dehn.orderedCofaceParity number
          ((A.bands (A.bridgeLabelling i).1).coface (A.bridgeLabelling i).2).val
          ((A.bands (A.bridgeLabelling i).1).ends 0).val
          ((A.bands (A.bridgeLabelling i).1).ends 1).val) +
        orientationSignParity (SignType.sign
          (ell (sm (A.bridgeEnd i)) - ell (sm (A.bridgeBegin i)))) = eps := by
  have hbound : ∀ t ∈ K.faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, htu, huc⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  have hfPL : FinitePiecewiseAffineOn f Sq := ⟨L, hL, hLs, hf⟩
  have hmap : MapsTo f L.space A.carrier := by
    intro x hx
    rw [hval ⟨x, hLs ▸ hx⟩]
    exact (C ⟨x, hLs ▸ hx⟩).property
  obtain ⟨α, β, hα, hαβ, hβ, hstart, hfinish, himage, hsourceInj, hinterior⟩ :=
    A.exists_marked_square_bridge_parameters hbound C f hfPL hval hmark i
  have hbridge : ∀ q ∈ Ioo α β,
      f (unitSquareSide i q) ∈ A.boundaryBridge i \ {A.bridgeBegin i, A.bridgeEnd i} := by
    intro q hq
    exact (hinterior q ⟨by linarith [hq.1], by linarith [hq.2]⟩).mpr hq
  obtain ⟨q, r, s, t, hq, hqrs, hrs, he, het, ho, hra, hsb⟩ :=
    A.exists_refined_bridge_edge_sample hpure L hL hLs f hf hF hmap hfaces O
      i α β hα hαβ hβ hbridge
  let B := A.bands (A.bridgeLabelling i).1
  let v : E := (B.ends 0).val
  let w : E := (B.ends 1).val
  let a := unitSquareSide i r
  let b := unitSquareSide i s
  have hab : a ≠ b := fun h ↦ hrs.ne (unitSquareSide_injective i h)
  have hvw : v ≠ w := fun h ↦ B.ends_ne (Subtype.ext h)
  have heT : ({v, w} : Finset E) ⊆ (O.owner t).val := by
    rw [ho]
    simpa [v, w, B.edge_eq] using B.edge_subset (A.bridgeLabelling i).2
  obtain ⟨c, hc, hct⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨heT, by simp [hvw, (O.owner t).property.2]⟩
  have hcne : c ≠ v ∧ c ≠ w := by simpa using hc
  have howner : (O.owner t).val = {v, w, c} := by
    rw [← hct]
    ext z
    simp [or_comm, or_left_comm]
  obtain ⟨x, hx, hxt⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨het, by change ({a, b} : Finset (ℝ × ℝ)).card + 1 = t.val.card
             simp [hab, t.property.2]⟩
  have hxne : x ≠ a ∧ x ≠ b := by simpa only [a, b, Finset.mem_insert,
    Finset.mem_singleton, not_or] using hx
  have hxm : x ∈ t.val := hxt ▸ Finset.mem_insert_self _ _
  obtain ⟨r₀, r₁, hr₀, hr₁⟩ := exists_original_edge_parameters v w
    (sm (f a)) (sm (f b)) hra hsb
  have hpar := O.signed_edge_scalar_parity t a b x (het (by simp [a]))
    (het (by simp [b])) hxm hab hxne.1.symm hxne.2.symm
    v w c howner hvw hcne.1.symm hcne.2.symm r₀ r₁ hr₀ hr₁
  have hell' : ell (w - v) = 1 := hell
  have hrval : ell (sm (f a)) - ell v = r₀ := by
    have h := congrArg ell hr₀
    simpa only [map_sub, map_smul, smul_eq_mul, hell', mul_one] using h
  have hsval : ell (sm (f b)) - ell v = r₁ := by
    have h := congrArg ell hr₁
    simpa only [map_sub, map_smul, smul_eq_mul, hell', mul_one] using h
  let g : ℝ → ℝ := fun u ↦ ell (sm (f (unitSquareSide i u)))
  have hdiff : g s - g r = r₁ - r₀ := by dsimp [g, a, b] at *; linarith
  obtain ⟨hgc, hgi⟩ := A.scalar_bridge_chart i f hfPL α β hα hαβ hβ
    himage hsourceInj ell helli
  obtain ⟨G, hG⟩ := hF t.val t.property.1
  let side : ℝ →ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineMap.lineMap (unitSquareSide i 0) (unitSquareSide i 1)
  have hside (u : ℝ) : side u = unitSquareSide i u := by
    change AffineMap.lineMap (unitSquareSide i 0) (unitSquareSide i 1) u = _
    simpa only [AffineMap.lineMap_apply_ring, sub_zero, mul_zero, mul_one, zero_add] using
      (unitSquareSide_lineMap i 0 1 u).symm
  have hsmap : MapsTo side (Icc r s) (convexHull ℝ (t.val : Set (ℝ × ℝ))) := by
    intro u hu
    apply ((convex_convexHull ℝ (t.val : Set (ℝ × ℝ))).affine_preimage
      side.toAffineMap).segment_subset
        (show side r ∈ convexHull ℝ (t.val : Set (ℝ × ℝ)) from
          (hside r).symm ▸ subset_convexHull ℝ _ (het (by simp)))
        (show side s ∈ convexHull ℝ (t.val : Set (ℝ × ℝ)) from
          (hside s).symm ▸ subset_convexHull ℝ _ (het (by simp)))
    exact Icc_subset_segment hu
  let H : ℝ →ᵃ[ℝ] ℝ := ell.toLinearMap.toAffineMap.comp
    (G.toAffineMap.comp side.toAffineMap)
  have hEq : EqOn g H (Icc r s) := by
    intro u hu
    change ell (sm (f (unitSquareSide i u))) = ell (G (side u))
    apply congrArg ell
    rw [hside]
    exact hG (by simpa only [hside] using hsmap hu)
  have hsgn := scalar_interval_direction_of_affine_overlap H hgc hgi hEq hq hqrs
  have hends : SignType.sign (ell (sm (A.bridgeEnd i)) - ell (sm (A.bridgeBegin i))) =
      SignType.sign (r₁ - r₀) := by
    have hgα : g α = ell (sm (A.bridgeBegin i)) := by simp only [g, hstart]
    have hgβ : g β = ell (sm (A.bridgeEnd i)) := by simp only [g, hfinish]
    rw [← hgα, ← hgβ, hsgn, ← hEq (right_mem_Icc.mpr hrs.le),
      ← hEq (left_mem_Icc.mpr hrs.le), hdiff]
  refine ⟨?_, ?_⟩
  · intro hz
    have heq : g β = g α := by
      change ell (sm (f (unitSquareSide i β))) = ell (sm (f (unitSquareSide i α)))
      rw [hstart, hfinish]
      exact sub_eq_zero.mp hz
    exact hαβ.ne' (hgi (right_mem_Icc.mpr hαβ.le) (left_mem_Icc.mpr hαβ.le) heq)
  · rw [hends]
    have h := hpar.2.symm.trans (hsign t i r s he het hrs)
    simpa only [ho, v, w, B] using h

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
