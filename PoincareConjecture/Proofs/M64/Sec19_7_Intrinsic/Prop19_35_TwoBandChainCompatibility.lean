import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandChainCompatibility

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_two_band_chains_faces_canonical
    {n0 n1 : ℕ}
    (F : Fin n0 ⊕ Fin n1 → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (lo : Fin n0 ⊕ Fin n1 → ℝ → ℝ)
    (a b ua wa ub wb ra rb : Fin n0 ⊕ Fin n1 → ℝ)
    (B : ∀ i, ObliqueBandFaces (F i) (lo i) (a i) (b i)
      (ua i) (wa i) (ub i) (wb i) (ra i) (rb i))
    (cut0 : Fin (n0 + 1) → Set AnnulusCoordinates)
    (hleft0 : ∀ i, (B (.inl i)).leftCut = cut0 i.castSucc)
    (hright0 : ∀ i, (B (.inl i)).rightCut = cut0 i.succ)
    (hsep0 : ∀ i j : Fin n0, i.succ < j.castSucc →
      Disjoint (B (.inl i)).carrier (B (.inl j)).carrier)
    (hadj0 : ∀ i j : Fin n0, i.succ = j.castSucc →
      (B (.inl i)).carrier ∩ (B (.inl j)).carrier = cut0 i.succ)
    (cut1 : Fin (n1 + 1) → Set AnnulusCoordinates)
    (hleft1 : ∀ i, (B (.inr i)).leftCut = cut1 i.castSucc)
    (hright1 : ∀ i, (B (.inr i)).rightCut = cut1 i.succ)
    (hsep1 : ∀ i j : Fin n1, i.succ < j.castSucc →
      Disjoint (B (.inr i)).carrier (B (.inr j)).carrier)
    (hadj1 : ∀ i j : Fin n1, i.succ = j.castSucc →
      (B (.inr i)).carrier ∩ (B (.inr j)).carrier = cut1 i.succ)
    (hcross : ∀ (i : Fin n0) (j : Fin n1),
      Disjoint (B (.inl i)).carrier (B (.inr j)).carrier) :
    ∀ (p q : (i : Fin n0 ⊕ Fin n1) × (Fin (B i).interface.count × Bool)), p ≠ q →
      CoordinateTriangleBoundaryIntersection
        ((B p.1).faceCoordinates p.2) ((B q.1).faceCoordinates q.2)
        ((B p.1).faceBasis p.2) ((B q.1).faceBasis q.2) := by
  have h0 := m64Intrinsic_band_chain_faces_canonical _ _ _ _ _ _ _ _ _ _
    (fun i : Fin n0 => B (.inl i)) cut0 hleft0 hright0 hsep0 hadj0
  have h1 := m64Intrinsic_band_chain_faces_canonical _ _ _ _ _ _ _ _ _ _
    (fun i : Fin n1 => B (.inr i)) cut1 hleft1 hright1 hsep1 hadj1
  rintro ⟨i, p⟩ ⟨j, q⟩ hpq
  rcases i with i | i <;> rcases j with j | j
  · apply h0 ⟨i, p⟩ ⟨j, q⟩
    intro h
    apply hpq
    exact congrArg
      (fun x : (k : Fin n0) × (Fin (B (.inl k)).interface.count × Bool) =>
        (⟨.inl x.1, x.2⟩ :
          (k : Fin n0 ⊕ Fin n1) × (Fin (B k).interface.count × Bool))) h
  · apply CoordinateTriangleBoundaryIntersection.disjoint
    rw [← (B (.inl i)).face_carrier_eq_coordinates,
      ← (B (.inr j)).face_carrier_eq_coordinates]
    exact (hcross i j).mono (fun _ hx => mem_iUnion.mpr ⟨p, hx⟩)
      (fun _ hx => mem_iUnion.mpr ⟨q, hx⟩)
  · apply CoordinateTriangleBoundaryIntersection.disjoint
    rw [← (B (.inr i)).face_carrier_eq_coordinates,
      ← (B (.inl j)).face_carrier_eq_coordinates]
    exact (hcross j i).symm.mono (fun _ hx => mem_iUnion.mpr ⟨p, hx⟩)
      (fun _ hx => mem_iUnion.mpr ⟨q, hx⟩)
  · apply h1 ⟨i, p⟩ ⟨j, q⟩
    intro h
    apply hpq
    exact congrArg
      (fun x : (k : Fin n1) × (Fin (B (.inr k)).interface.count × Bool) =>
        (⟨.inr x.1, x.2⟩ :
          (k : Fin n0 ⊕ Fin n1) × (Fin (B k).interface.count × Bool))) h

end PoincareConjecture
