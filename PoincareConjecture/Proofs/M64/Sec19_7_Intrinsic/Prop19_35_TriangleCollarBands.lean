import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCollar
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCollarBands

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace PoincareConjecture

namespace M64IntrinsicCornerArcCollar

theorem lower_subset_original
    {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
    {U : Set AnnulusCoordinates} {C : M64IntrinsicFiniteCornerCaps alpha beta A B U}
    {corner : Bool → J} {sigma : ℝ → AnnulusCoordinates} {T : ℝ}
    (D : M64IntrinsicCornerArcCollar C corner sigma T) (i : Fin D.chain.count) :
    (D.chain.band i).lowerArc ⊆ sigma '' Icc 0 T := by
  apply (D.chain.lower_subset i).trans
  have hfull : (fun t => sigma (if D.reversed then T - t else t)) '' Icc 0 T =
      sigma '' Icc 0 T := by
    cases D.reversed
    · rfl
    · change (sigma ∘ fun t => T - t) '' Icc 0 T = _
      rw [image_comp, image_const_sub_Icc]
      simp only [sub_self, sub_zero]
  apply Subset.trans (image_mono (Icc_subset_Icc (C.radius_pos _).le
    (sub_le_self _ (C.radius_pos _).le)))
  exact hfull.subset

end M64IntrinsicCornerArcCollar

namespace M64IntrinsicTriangleCollar

variable {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicTriangleCaps base alpha beta D A B U} (P : M64IntrinsicTriangleCollar C)

abbrev BandIndex := Fin P.baseArc.chain.count ⊕
  (Fin P.firstSide.chain.count ⊕ Fin P.secondSide.chain.count)

def bandData : P.BandIndex → M64IntrinsicLinearBandData
  | .inl i => .ofChain P.baseArc.chain i
  | .inr (.inl i) => .ofChain P.firstSide.chain i
  | .inr (.inr i) => .ofChain P.secondSide.chain i

theorem band_union : (⋃ i, (P.bandData i).band.carrier) =
    P.baseArc.bands ∪ (P.firstSide.bands ∪ P.secondSide.bands) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    rcases i with i | (i | i)
    · exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
    · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨i, hi⟩))
    · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨i, hi⟩))
  · rintro (hp | (hp | hp))
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨.inl i, hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨.inr (.inl i), hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨.inr (.inr i), hi⟩

theorem band_subset (i : P.BandIndex) : (P.bandData i).band.carrier ⊆ P.carrier := by
  intro p hp
  apply Or.inr
  rw [← P.band_union]
  exact mem_iUnion.mpr ⟨i, hp⟩

theorem band_lower_subset
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (i : P.BandIndex) : (P.bandData i).band.lowerArc ⊆ frontier U := by
  rw [hfront]
  rcases i with i | (i | i)
  · exact (P.baseArc.lower_subset_original i).trans subset_union_left
  · exact (P.firstSide.lower_subset_original i).trans
      (subset_union_left.trans subset_union_right)
  · exact (P.secondSide.lower_subset_original i).trans
      (subset_union_right.trans subset_union_right)

end M64IntrinsicTriangleCollar

end PoincareConjecture
