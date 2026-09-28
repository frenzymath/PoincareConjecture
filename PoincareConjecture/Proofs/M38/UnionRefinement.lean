import PoincareConjecture.Proofs.M38.OneCapAssembly
import PoincareConjecture.Proofs.M38.RegionEquivalences









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38


def restrictRegions {A B : GeneralizedSliceCarrier.{u}}
    {U : Set A.carrier} {V : Set B.carrier}
    (e : SurgeryRegionEquivalence A B U V) (W : Set A.carrier) (hW : W ⊆ U) :
    SurgeryRegionEquivalence A B W (e.map '' W) where
  map := e.map
  inverse := e.inverse
  map_image := rfl
  inverse_image := e.left_inverse.image_image' hW
  left_inverse := e.left_inverse.mono hW
  right_inverse := e.right_inverse.mono
    (fun _ hy => e.map_image.subset (Set.image_mono hW hy))
  map_smooth := e.map_smooth.mono hW
  inverse_smooth := e.inverse_smooth.mono
    (fun _ hy => e.map_image.subset (Set.image_mono hW hy))



noncomputable def sumRefinement {m n : ℕ}
    {piecesB : Fin m → GeneralizedSliceCarrier.{u}}
    {piecesD : Fin n → GeneralizedSliceCarrier.{u}}
    {B D : GeneralizedSliceCarrier.{u}}
    (UB : SmoothDisjointUnionData piecesB B) (UD : SmoothDisjointUnionData piecesD D)
    (hB : Nonempty B.carrier) (hD : Nonempty D.carrier) :
    SmoothDisjointUnionData (Fin.append piecesB piecesD) (sumCarrier B D) := by
  refine {
    region := Fin.append (fun i => Sum.inl '' UB.region i) (fun i => Sum.inr '' UD.region i)
    region_open := ?_
    region_closed := ?_
    identify := ?_
    pairwise_disjoint := ?_
    cover := ?_ }
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Fin.append_left]
      exact isOpenMap_inl _ (UB.region_open j)
    · intro j
      simp only [Fin.append_right]
      exact isOpenMap_inr _ (UD.region_open j)
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Fin.append_left]
      exact isClosedMap_inl _ (UB.region_closed j)
    · intro j
      simp only [Fin.append_right]
      exact isClosedMap_inr _ (UD.region_closed j)
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [Fin.append_left, Fin.append_left]
      exact composeRegions (UB.identify j)
        (restrictRegions (sumInlEquivalence B D hB) (UB.region j) (Set.subset_univ _))
    · intro j
      rw [Fin.append_right, Fin.append_right]
      exact composeRegions (UD.identify j)
        (restrictRegions (sumInrEquivalence B D hD) (UD.region j) (Set.subset_univ _))
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i j
      refine Fin.addCases ?_ ?_ j
      · intro j hij
        simp only [Fin.append_left]
        exact (Set.disjoint_image_iff Sum.inl_injective).mpr
          (UB.pairwise_disjoint i j (fun h => hij (congrArg (Fin.castAdd n) h)))
      · intro j _
        simp only [Fin.append_left, Fin.append_right]
        apply Set.disjoint_left.mpr
        rintro _ ⟨x, _, rfl⟩ ⟨y, _, he⟩
        cases he
    · intro i j
      refine Fin.addCases ?_ ?_ j
      · intro j _
        simp only [Fin.append_left, Fin.append_right]
        apply Set.disjoint_left.mpr
        rintro _ ⟨x, _, rfl⟩ ⟨y, _, he⟩
        cases he
      · intro j hij
        simp only [Fin.append_right]
        exact (Set.disjoint_image_iff Sum.inr_injective).mpr
          (UD.pairwise_disjoint i j (fun h => hij (congrArg (Fin.natAdd m) h)))
  · apply Set.eq_univ_of_forall
    intro x
    cases x with
    | inl x =>
        have hx : x ∈ ⋃ i, UB.region i := UB.cover.symm ▸ Set.mem_univ x
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        apply Set.mem_iUnion.mpr
        refine ⟨Fin.castAdd n i, ?_⟩
        simp only [Fin.append_left]
        exact ⟨x, hi, rfl⟩
    | inr x =>
        have hx : x ∈ ⋃ i, UD.region i := UD.cover.symm ▸ Set.mem_univ x
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        apply Set.mem_iUnion.mpr
        refine ⟨Fin.natAdd m i, ?_⟩
        simp only [Fin.append_right]
        exact ⟨x, hi, rfl⟩

end PoincareConjecture.M38
