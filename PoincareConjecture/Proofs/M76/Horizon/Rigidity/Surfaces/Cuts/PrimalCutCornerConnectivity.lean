import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutArcPairing
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.BoundaryPairing

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

def arcEndpointCorner (i : Fin 4) (j : Fin 2) : Fin 4 := if j = 0 then i-1 else i

noncomputable def arcEndpointSource (i : Fin 4) (j : Fin 2) : E :=
  A.sourceMap K P D hD hcofaces hP labels (if j = 0 then A.bridgeBegin i else A.bridgeEnd i)

def originalCornerStep (a b : Fin 4) : Prop :=
  ∃ (i : Fin 4) (j k : Fin 2), a = arcEndpointCorner i j ∧
    b = arcEndpointCorner (A.arcPairing i) k ∧
    A.arcEndpointSource i j = A.arcEndpointSource (A.arcPairing i) k

theorem source_bridge_begin_ne_end (i : Fin 4) :
    A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin i) ≠
      A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i) := by
  intro he
  have hc := A.sourceMap_injOn_boundaryBridge i
    ((A.boundaryBridge_interval i).1 (Or.inl rfl))
    ((A.boundaryBridge_interval i).1 (Or.inr rfl)) he
  have hn := (A.boundaryBridge_interval i).ncard_boundary_eq_two
  rw [hc,pair_eq_singleton,Set.ncard_singleton] at hn
  norm_num at hn

theorem arcEndpointSource_injective (i : Fin 4) : Function.Injective (A.arcEndpointSource i) := by
  intro j k he
  fin_cases j <;> fin_cases k
  · rfl
  · exact (A.source_bridge_begin_ne_end i he).elim
  · exact (A.source_bridge_begin_ne_end i he.symm).elim
  · rfl

theorem arcEndpointSource_eq_original_mark (i : Fin 4) (j : Fin 2) :
    ∃ k : Fin 2, A.arcEndpointSource i j =
      originalExteriorMarks K P D hcofaces A.bands labels
        ((exteriorFourIndex K P D labels).symm ((A.bridgeLabelling i).1,k)) := by
  have hx : A.arcEndpointSource i j ∈
      ({A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin i),
        A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i)} : Set E) := by
    fin_cases j <;> simp [arcEndpointSource]
  rw [A.source_bridge_endpoints] at hx
  rcases hx with hx | hx
  · exact ⟨0,hx.trans (originalExteriorMarks_apply_inverse K P D hcofaces A.bands labels _ 0).symm⟩
  · exact ⟨1,hx.trans (originalExteriorMarks_apply_inverse K P D hcofaces A.bands labels _ 1).symm⟩

theorem arc_eq_or_paired_of_endpoint_source_eq {i k : Fin 4} {j l : Fin 2}
    (he : A.arcEndpointSource i j = A.arcEndpointSource k l) : k = i ∨ k = A.arcPairing i := by
  obtain ⟨a,ha⟩ := A.arcEndpointSource_eq_original_mark i j
  obtain ⟨b,hb⟩ := A.arcEndpointSource_eq_original_mark k l
  have hm := originalExteriorMarks_injective K P D hcofaces A.bands labels
    (ha.symm.trans (he.trans hb))
  have hp := (exteriorFourIndex K P D labels).symm.injective hm
  have hfst := congrArg (fun p : ResidualHalfBandIndex K P D => p.1) hp
  have hd : (A.bridgeLabelling k).2 = (A.bridgeLabelling i).2 ∨
      (A.bridgeLabelling k).2 = (A.bridgeLabelling i).2+1 := by
    generalize (A.bridgeLabelling k).2 = x
    generalize (A.bridgeLabelling i).2 = y
    fin_cases x <;> fin_cases y <;> decide
  rcases hd with hd | hd
  · exact Or.inl (A.bridgeLabelling.injective (Prod.ext hfst.symm hd))
  · apply Or.inr
    apply A.bridgeLabelling.injective
    rw [A.arcPairing_label]
    exact Prod.ext hfst.symm hd

theorem endpoint_source_eq_corner_related {i k : Fin 4} {j l : Fin 2}
    (he : A.arcEndpointSource i j = A.arcEndpointSource k l) :
    Relation.EqvGen A.originalCornerStep (arcEndpointCorner i j) (arcEndpointCorner k l) := by
  rcases A.arc_eq_or_paired_of_endpoint_source_eq he with hk | hk
  · subst k
    have h : j = l := A.arcEndpointSource_injective i he
    subst l
    exact Relation.EqvGen.refl _
  · subst k
    exact Relation.EqvGen.rel _ _ ⟨i,j,l,rfl,rfl,he⟩

theorem exists_corner_endpoint_of_original_spoke (a t : Fin 4)
    (ht : t ∈ ({A.matching a,A.matching a+1} : Set (Fin 4))) :
    ∃ (i : Fin 4) (j : Fin 2), arcEndpointCorner i j = a ∧
      A.arcEndpointSource i j =
        originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order t) := by
  obtain ⟨l,r,hlr,_,_,hl,hr⟩ := A.exists_gapSpoke_original_indices a
  rw [← hlr] at ht
  rcases ht with ht | ht
  · subst t
    exact ⟨a,1,by simp [arcEndpointCorner],hl.symm⟩
  · subst t
    refine ⟨a+1,0,?_,hr.symm⟩
    simp [arcEndpointCorner]

theorem consecutive_original_sectors_corner_related (t : Fin 4) :
    Relation.EqvGen A.originalCornerStep (A.matching.symm (t-1)) (A.matching.symm t) := by
  obtain ⟨i,j,hij,hmark⟩ := A.exists_corner_endpoint_of_original_spoke (A.matching.symm (t-1)) t
    (by simp)
  obtain ⟨k,l,hkl,hmark'⟩ := A.exists_corner_endpoint_of_original_spoke (A.matching.symm t) t
    (by simp)
  rw [← hij,← hkl]
  exact A.endpoint_source_eq_corner_related (hmark.trans hmark'.symm)

theorem originalCornerStep_connected :
    ∀ a b, Relation.EqvGen A.originalCornerStep a b := by
  have h01 : Relation.EqvGen A.originalCornerStep (A.matching.symm 0) (A.matching.symm 1) :=
    A.consecutive_original_sectors_corner_related 1
  have h12 : Relation.EqvGen A.originalCornerStep (A.matching.symm 1) (A.matching.symm 2) :=
    A.consecutive_original_sectors_corner_related 2
  have h23 : Relation.EqvGen A.originalCornerStep (A.matching.symm 2) (A.matching.symm 3) :=
    A.consecutive_original_sectors_corner_related 3
  have h0 (t : Fin 4) : Relation.EqvGen A.originalCornerStep (A.matching.symm 0) (A.matching.symm t) := by
    fin_cases t
    · exact Relation.EqvGen.refl _
    · exact h01
    · exact Relation.EqvGen.trans _ _ _ h01 h12
    · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ h01 h12) h23
  intro a b
  have ha := h0 (A.matching a)
  have hb := h0 (A.matching b)
  simp only [A.matching.symm_apply_apply] at ha hb
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ha) hb

theorem originalCornerStep_reversing_shift
    (hreverse : ∀ i, A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin (A.arcPairing i)) =
      A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i))
    {a b : Fin 4} (hab : A.originalCornerStep a b) :
    Relation.EqvGen (reversingCornerStep A.arcPairing) (a+1) (b+1) := by
  obtain ⟨i,j,k,rfl,rfl,he⟩ := hab
  fin_cases j <;> fin_cases k
  · change A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin i) =
      A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin (A.arcPairing i)) at he
    exact (A.source_bridge_begin_ne_end i (he.trans (hreverse i))).elim
  · change Relation.EqvGen (reversingCornerStep A.arcPairing) (i-1+1) (A.arcPairing i+1)
    rw [sub_add_cancel]
    exact Relation.EqvGen.rel _ _ rfl
  · change Relation.EqvGen (reversingCornerStep A.arcPairing) (i+1) (A.arcPairing i-1+1)
    rw [sub_add_cancel]
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    change i+1 = A.arcPairing (A.arcPairing i)+1
    rw [A.arcPairing_involutive]
  · change A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i) =
      A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd (A.arcPairing i)) at he
    have hp := hreverse (A.arcPairing i)
    rw [A.arcPairing_involutive] at hp
    exact (A.source_bridge_begin_ne_end i (hp.trans he.symm)).elim

theorem reversingCornerStep_connected_of_source_reversal
    (hreverse : ∀ i, A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin (A.arcPairing i)) =
      A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i)) :
    ∀ i j, Relation.EqvGen (reversingCornerStep A.arcPairing) i j := by
  have hmap {a b : Fin 4} (hab : Relation.EqvGen A.originalCornerStep a b) :
      Relation.EqvGen (reversingCornerStep A.arcPairing) (a+1) (b+1) := by
    induction hab with
    | rel a b hab => exact A.originalCornerStep_reversing_shift hreverse hab
    | refl a => exact Relation.EqvGen.refl _
    | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
  intro i j
  simpa only [sub_add_cancel] using hmap (A.originalCornerStep_connected (i-1) (j-1))

theorem arcPairing_opposite_of_source_reversal
    (hreverse : ∀ i, A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin (A.arcPairing i)) =
      A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i)) :
    ∀ i, A.arcPairing i = i+2 :=
  reversing_one_vertex_pairing_opposite A.arcPairing A.arcPairing_involutive A.arcPairing_ne
    (A.reversingCornerStep_connected_of_source_reversal hreverse)

end OriginalPrimalCutDiskData
end PoincareConjecture.M76.OriginalTriangleCopies
