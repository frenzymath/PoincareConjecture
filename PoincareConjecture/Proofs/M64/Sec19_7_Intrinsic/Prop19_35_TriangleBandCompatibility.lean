import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCollarBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcBandCompatibility




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture.M64IntrinsicTriangleCollar





theorem band_faces_canonical
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicTriangleCaps base alpha beta D A B U} (P : M64IntrinsicTriangleCollar C)
    (p q : (i : P.BandIndex) × (Fin (P.bandData i).band.interface.count × Bool))
    (hpq : p ≠ q) :
    CoordinateTriangleBoundaryIntersection ((P.bandData p.1).band.faceCoordinates p.2)
      ((P.bandData q.1).band.faceCoordinates q.2) ((P.bandData p.1).band.faceBasis p.2)
      ((P.bandData q.1).band.faceBasis q.2) := by
  have h01 (i : Fin P.baseArc.chain.count) (j : Fin P.firstSide.chain.count) :
      Disjoint (P.baseArc.chain.band i).carrier (P.firstSide.chain.band j).carrier :=
    P.base_first.mono (fun _ hp => mem_iUnion.mpr ⟨i, hp⟩)
      (fun _ hp => mem_iUnion.mpr ⟨j, hp⟩)
  have h02 (i : Fin P.baseArc.chain.count) (j : Fin P.secondSide.chain.count) :
      Disjoint (P.baseArc.chain.band i).carrier (P.secondSide.chain.band j).carrier :=
    P.base_second.mono (fun _ hp => mem_iUnion.mpr ⟨i, hp⟩)
      (fun _ hp => mem_iUnion.mpr ⟨j, hp⟩)
  have h12 (i : Fin P.firstSide.chain.count) (j : Fin P.secondSide.chain.count) :
      Disjoint (P.firstSide.chain.band i).carrier (P.secondSide.chain.band j).carrier :=
    P.first_second.mono (fun _ hp => mem_iUnion.mpr ⟨i, hp⟩)
      (fun _ hp => mem_iUnion.mpr ⟨j, hp⟩)
  rcases p with ⟨i | (i | i), p⟩
  · rcases q with ⟨j | (j | j), q⟩
    · exact P.baseArc.chain.faces_canonical ⟨i, p⟩ ⟨j, q⟩
        (fun h => hpq (by cases h; rfl))
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain P.baseArc.chain i) (.ofChain P.firstSide.chain j) (h01 i j) p q
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain P.baseArc.chain i) (.ofChain P.secondSide.chain j) (h02 i j) p q
  · rcases q with ⟨j | (j | j), q⟩
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain P.firstSide.chain i) (.ofChain P.baseArc.chain j) (h01 j i).symm p q
    · exact P.firstSide.chain.faces_canonical ⟨i, p⟩ ⟨j, q⟩
        (fun h => hpq (by cases h; rfl))
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain P.firstSide.chain i) (.ofChain P.secondSide.chain j) (h12 i j) p q
  · rcases q with ⟨j | (j | j), q⟩
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain P.secondSide.chain i) (.ofChain P.baseArc.chain j) (h02 j i).symm p q
    · exact M64IntrinsicLinearBandData.faces_canonical_of_disjoint
        (.ofChain P.secondSide.chain i) (.ofChain P.firstSide.chain j) (h12 j i).symm p q
    · exact P.secondSide.chain.faces_canonical ⟨i, p⟩ ⟨j, q⟩
        (fun h => hpq (by cases h; rfl))

end PoincareConjecture.M64IntrinsicTriangleCollar
