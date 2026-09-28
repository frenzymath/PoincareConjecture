import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCollarBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandChainCompatibility





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

namespace M64IntrinsicLinearBandData




theorem faces_canonical_of_disjoint (B E : M64IntrinsicLinearBandData)
    (h : Disjoint B.band.carrier E.band.carrier)
    (i : Fin B.band.interface.count × Bool) (j : Fin E.band.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection (B.band.faceCoordinates i) (E.band.faceCoordinates j)
      (B.band.faceBasis i) (E.band.faceBasis j) := by
  apply CoordinateTriangleBoundaryIntersection.disjoint
  rw [← B.band.face_carrier_eq_coordinates, ← E.band.face_carrier_eq_coordinates]
  exact h.mono (fun _ hp => mem_iUnion.mpr ⟨i, hp⟩) (fun _ hp => mem_iUnion.mpr ⟨j, hp⟩)

end M64IntrinsicLinearBandData

namespace M64IntrinsicArcBandChain




theorem faces_canonical {gamma : ℝ → AnnulusCoordinates} {a b : ℝ}
    {U : Set AnnulusCoordinates} (E : M64IntrinsicArcBandChain gamma a b U)
    (p q : (i : Fin E.count) × (Fin (E.band i).interface.count × Bool)) (hpq : p ≠ q) :
    CoordinateTriangleBoundaryIntersection ((E.band p.1).faceCoordinates p.2)
      ((E.band q.1).faceCoordinates q.2) ((E.band p.1).faceBasis p.2)
      ((E.band q.1).faceBasis q.2) :=
  m64Intrinsic_band_chain_faces_canonical _ _ _ _ _ _ _ _ _ _ E.band
    (fun k => segment ℝ (gamma (E.cut k)) (gamma (E.cut k) + E.length • E.direction (E.cut k)))
    E.left_cut E.right_cut E.separated E.adjacent p q hpq

end M64IntrinsicArcBandChain

namespace M64IntrinsicJoinedBandPatch




theorem faces_canonical {gamma : Bool → ℝ → AnnulusCoordinates} {T b : Bool → ℝ}
    {U : Set AnnulusCoordinates} (P : M64IntrinsicJoinedBandPatch gamma T b U)
    (p q : (e : Bool) × (Fin (P.band e).interface.count × Bool)) (hpq : p ≠ q) :
    CoordinateTriangleBoundaryIntersection ((P.band p.1).faceCoordinates p.2)
      ((P.band q.1).faceCoordinates q.2) ((P.band p.1).faceBasis p.2)
      ((P.band q.1).faceBasis q.2) := by
  have hcross (i : Fin (P.band false).interface.count × Bool)
      (j : Fin (P.band true).interface.count × Bool) :=
    m64Intrinsic_shared_cut_bands_canonical_compatibility (P.band false) (P.band true) true false
      (by
        rw [(P.band false).endpointEdge_image]
        exact P.intersection.trans (P.inner_cut false).symm)
      (by rw [(P.band false).endpointEdge_image, (P.band true).endpointEdge_image]
          exact (P.inner_cut false).trans (P.inner_cut true).symm) i j
  rcases p with ⟨e, i⟩
  rcases q with ⟨f, j⟩
  cases e <;> cases f
  · exact m64Intrinsic_band_faces_canonical_compatibility (P.band false) i j
      (fun h => hpq (by cases h; rfl))
  · exact hcross i j
  · exact (hcross j i).symm
  · exact m64Intrinsic_band_faces_canonical_compatibility (P.band true) i j
      (fun h => hpq (by cases h; rfl))

end M64IntrinsicJoinedBandPatch

namespace M64IntrinsicJoinedArcCollar





theorem chain_patch_faces_canonical
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
    (J : M64IntrinsicJoinedArcCollar C b) (e : Bool) (i : Fin (J.chain e).count)
    (f : Bool) (p : Fin ((J.chain e).band i).interface.count × Bool)
    (q : Fin (J.patch.band f).interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection (((J.chain e).band i).faceCoordinates p)
      ((J.patch.band f).faceCoordinates q) (((J.chain e).band i).faceBasis p)
      ((J.patch.band f).faceBasis q) := by
  by_cases hef : e = f
  · subst f
    by_cases hattach : (J.chain e).cut (if e then i.castSucc else i.succ) = b e
    · have hshared : ((J.patch.band e).endpointEdge e).map '' Icc (0 : ℝ) 1 =
          (((J.chain e).band i).endpointEdge (!e)).map '' Icc (0 : ℝ) 1 := by
        rw [(J.patch.band e).endpointEdge_image, ((J.chain e).band i).endpointEdge_image,
          J.matched_cut]
        cases e
        · change _ = ((J.chain false).band i).rightCut
          change (J.chain false).cut i.succ = b false at hattach
          rw [(J.chain false).right_cut, hattach]
        · change _ = ((J.chain true).band i).leftCut
          change (J.chain true).cut i.castSucc = b true at hattach
          rw [(J.chain true).left_cut, hattach]
      have hinter : (J.patch.band e).carrier ∩ ((J.chain e).band i).carrier =
          ((J.patch.band e).endpointEdge e).map '' Icc (0 : ℝ) 1 := by
        rw [hshared, ((J.chain e).band i).endpointEdge_image, J.patch_contact]
        cases e <;> exact if_pos hattach
      exact (m64Intrinsic_shared_cut_bands_canonical_compatibility (J.patch.band e)
        ((J.chain e).band i) e (!e) hinter hshared q p).symm
    · have hd : Disjoint (J.patch.band e).carrier ((J.chain e).band i).carrier := by
        apply disjoint_iff_inter_eq_empty.mpr
        rw [J.patch_contact]
        cases e <;> exact if_neg hattach
      exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain (J.chain e) i) (.ofPatch J.patch e) hd.symm p q
  · have hf : f = !e := by cases e <;> cases f <;> simp_all
    subst f
    exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
      (.ofChain (J.chain e) i) (.ofPatch J.patch (!e)) (J.opposite_patch e i).symm p q

end M64IntrinsicJoinedArcCollar

namespace M64IntrinsicThreeArcCollar




theorem band_faces_canonical
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
    (D : M64IntrinsicThreeArcCollar C b)
    (p q : (i : D.BandIndex) × (Fin (D.bandData i).band.interface.count × Bool))
    (hpq : p ≠ q) :
    CoordinateTriangleBoundaryIntersection ((D.bandData p.1).band.faceCoordinates p.2)
      ((D.bandData q.1).band.faceCoordinates q.2) ((D.bandData p.1).band.faceBasis p.2)
      ((D.bandData q.1).band.faceBasis q.2) := by
  have hthirdChain (e : Bool) (i : Fin (D.joined.chain e).count) (j : Fin D.third.count) :
      Disjoint (D.third.band j).carrier ((D.joined.chain e).band i).carrier :=
    (D.separated j).mono_right fun _ hp => mem_iUnion.mpr ⟨e, Or.inl (mem_iUnion.mpr ⟨i, hp⟩)⟩
  have hthirdPatch (e : Bool) (j : Fin D.third.count) :
      Disjoint (D.third.band j).carrier (D.joined.patch.band e).carrier :=
    (D.separated j).mono_right fun _ hp => mem_iUnion.mpr ⟨e, Or.inr hp⟩
  rcases p with ⟨⟨e, i⟩ | (e | i), p⟩
  · rcases q with ⟨⟨f, j⟩ | (f | j), q⟩
    · by_cases hef : e = f
      · subst f
        exact (D.joined.chain e).faces_canonical ⟨i, p⟩ ⟨j, q⟩
          (fun h => hpq (by cases h; rfl))
      · have hd : Disjoint ((D.joined.chain e).band i).carrier
            ((D.joined.chain f).band j).carrier := by
          cases e <;> cases f
          · exact (hef rfl).elim
          · exact D.joined.chains_disjoint i j
          · exact (D.joined.chains_disjoint j i).symm
          · exact (hef rfl).elim
        exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
          (.ofChain (D.joined.chain e) i) (.ofChain (D.joined.chain f) j) hd p q
    · exact D.joined.chain_patch_faces_canonical e i f p q
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain (D.joined.chain e) i) (.ofChain D.third j) (hthirdChain e i j).symm p q
  · rcases q with ⟨⟨f, j⟩ | (f | j), q⟩
    · exact (D.joined.chain_patch_faces_canonical f j e q p).symm
    · exact D.joined.patch.faces_canonical ⟨e, p⟩ ⟨f, q⟩
        (fun h => hpq (by cases h; rfl))
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofPatch D.joined.patch e) (.ofChain D.third j) (hthirdPatch e j).symm p q
  · rcases q with ⟨⟨f, j⟩ | (f | j), q⟩
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain D.third i) (.ofChain (D.joined.chain f) j) (hthirdChain f j i) p q
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain D.third i) (.ofPatch D.joined.patch f) (hthirdPatch f i) p q
    · exact D.third.faces_canonical ⟨i, p⟩ ⟨j, q⟩ (fun h => hpq (by cases h; rfl))

end M64IntrinsicThreeArcCollar

end PoincareConjecture
