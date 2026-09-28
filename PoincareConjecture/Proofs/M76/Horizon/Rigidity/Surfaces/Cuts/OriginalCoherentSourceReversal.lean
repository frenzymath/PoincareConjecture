import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCoherentBridgeReversal



set_option autoImplicit false

open Set Geometry Classical AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

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

local notation "sm" => A.sourceMap K P D hD hcofaces hP labels



theorem source_bridge_reversal_of_original_coherent_signs
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sourceSign : Finset E → ZMod 2)
    (hcancel : ∀ T ∈ K.faces, ∀ U ∈ K.faces, T.card = 3 → U.card = 3 → T ≠ U →
      ∀ a b : E, a ≠ b → {a, b} ⊆ T → {a, b} ⊆ U →
      (sourceSign T + boundaryFaceParity number T {a, b}) +
        (sourceSign U + boundaryFaceParity number U {a, b}) = 1) :
    ∀ i : Fin 4, sm (A.bridgeBegin (A.arcPairing i)) = sm (A.bridgeEnd i) := by
  have hbound : ∀ t ∈ K.faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, htu, huc⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  obtain ⟨C, _, hbottom, htop, hleft, hright, f, L,
    hval, hL, hLs, hf, hF, hfaces, _, hO⟩ :=
    A.exists_marked_planar_original_refinement_with_orientation hbound hpure
      number hnumber sourceSign hcancel
  obtain ⟨refinedNumber, hrefined⟩ := finite_vertex_numbering L hL
  obtain ⟨O⟩ := hO refinedNumber hrefined
  obtain ⟨eps, hsign⟩ := O.exists_ccw_square_boundary_sign hL hLs hrefined
  have hmark (i : Fin 4) (x : PeriodicSquare.squareCarrier 1) :
      (C x).val ∈ A.longBoundaryArc i ↔
        ![x.val.2 = 0, x.val.1 = 1, x.val.2 = 1, x.val.1 = 0] i := by
    fin_cases i
    · exact hbottom x
    · exact hright x
    · exact htop x
    · exact hleft x
  intro i
  let B := A.bands (A.bridgeLabelling i).1
  let j := (A.bridgeLabelling i).2
  let v : E := (B.ends 0).val
  let w : E := (B.ends 1).val
  have hvw : v ≠ w := fun h => B.ends_ne (Subtype.ext h)
  obtain ⟨ell, hell, _, helli⟩ := exists_edge_scalar_coordinate v w hvw
  have hi := A.bridge_endpoint_scalar_parity hpure C f L hL hLs hf hF hfaces
    hval hmark O eps hsign i ell hell helli
  have hfirst : (A.bridgeLabelling (A.arcPairing i)).1 = (A.bridgeLabelling i).1 := by
    have hh := congrArg Prod.fst (A.arcPairing_label i)
    simpa only [residualSheetFlip, Equiv.coe_fn_mk] using hh
  have hsecond : (A.bridgeLabelling (A.arcPairing i)).2 = (A.bridgeLabelling i).2 + 1 :=
    congrArg Prod.snd (A.arcPairing_label i)
  have hellpair : ell (((A.bands (A.bridgeLabelling (A.arcPairing i)).1).ends 1).val -
      ((A.bands (A.bridgeLabelling (A.arcPairing i)).1).ends 0).val) = 1 := by
    rw [hfirst]
    exact hell
  have hellipair : InjOn ell (range (AffineMap.lineMap
      ((A.bands (A.bridgeLabelling (A.arcPairing i)).1).ends 0).val
      ((A.bands (A.bridgeLabelling (A.arcPairing i)).1).ends 1).val : ℝ → E)) := by
    rw [hfirst]
    exact helli
  have hj := A.bridge_endpoint_scalar_parity hpure C f L hL hLs hf hF hfaces
    hval hmark O eps hsign (A.arcPairing i) ell hellpair hellipair
  have hne' (k : Fin 2) : (B.coface k).val ≠ (B.coface (k + 1)).val := by
    intro heq
    have heq' := Subtype.ext heq
    fin_cases k
    · exact B.coface_ne heq'
    · exact B.coface_ne heq'.symm
  have hedge (k : Fin 2) : ({v, w} : Finset E) ⊆ (B.coface k).val := by
    simpa [v, w, B.edge_eq] using B.edge_subset k
  have hco := hcancel (B.coface j).val (B.coface j).property.1
    (B.coface (j + 1)).val (B.coface (j + 1)).property.1
    (B.coface j).property.2 (B.coface (j + 1)).property.2 (hne' j)
    v w hvw (hedge j) (hedge (j + 1))
  have hordered := Dehn.orderedCofaceParity_cancellation number
    (B.coface j).val (B.coface (j + 1)).val v w
    (sourceSign (B.coface j).val) (sourceSign (B.coface (j + 1)).val) hco
  rcases pair_eq_pair_iff.mp (A.source_bridge_endpoints_paired i) with ⟨h0, h1⟩ | hrev
  · have hi' := hi.2
    have hj' := hj.2
    rw [h0, h1] at hj'
    rw [hfirst, hsecond] at hj'
    change sourceSign (B.coface j).val + Dehn.orderedCofaceParity number
      (B.coface j).val v w + _ = eps at hi'
    change sourceSign (B.coface (j + 1)).val + Dehn.orderedCofaceParity number
      (B.coface (j + 1)).val v w + _ = eps at hj'
    have heq : sourceSign (B.coface j).val + Dehn.orderedCofaceParity number
        (B.coface j).val v w = sourceSign (B.coface (j + 1)).val +
          Dehn.orderedCofaceParity number (B.coface (j + 1)).val v w :=
      add_right_cancel (hi'.trans hj'.symm)
    rw [heq, CharTwo.add_self_eq_zero] at hordered
    exact (zero_ne_one hordered).elim
  · exact hrev.1

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
