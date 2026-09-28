import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCollar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

structure M64IntrinsicLinearBandData where
  frame : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates
  graph : ℝ → ℝ
  left : ℝ
  right : ℝ
  left_direction : ℝ × ℝ
  right_direction : ℝ × ℝ
  left_length : ℝ
  right_length : ℝ
  band : ObliqueBandFaces
    (collarParameterEquiv.trans frame).toHomeomorph.toOpenPartialHomeomorph
    graph left right left_direction.1 left_direction.2 right_direction.1 right_direction.2
    left_length right_length

namespace M64IntrinsicLinearBandData

def ofChain {gamma : ℝ → AnnulusCoordinates} {a b : ℝ} {U : Set AnnulusCoordinates}
    (E : M64IntrinsicArcBandChain gamma a b U) (i : Fin E.count) :
    M64IntrinsicLinearBandData where
  frame := (E.frame i).symm
  graph := E.graph i
  left := E.parameter i (E.cut i.castSucc)
  right := E.parameter i (E.cut i.succ)
  left_direction := E.frame i (E.direction (E.cut i.castSucc))
  right_direction := E.frame i (E.direction (E.cut i.succ))
  left_length := E.length
  right_length := E.length
  band := E.band i

def ofPatch {gamma : Bool → ℝ → AnnulusCoordinates} {T b : Bool → ℝ}
    {U : Set AnnulusCoordinates} (P : M64IntrinsicJoinedBandPatch gamma T b U) (e : Bool) :
    M64IntrinsicLinearBandData where
  frame := P.frame e
  graph := P.graph e
  left := P.left e
  right := P.right e
  left_direction := (P.frame e).symm P.direction
  right_direction := (P.frame e).symm P.direction
  left_length := if e then P.middle_length else P.left_length
  right_length := if e then P.right_length else P.middle_length
  band := P.band e

end M64IntrinsicLinearBandData

namespace M64IntrinsicThreeArcCollar

variable {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
  {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
  (D : M64IntrinsicThreeArcCollar C b)

abbrev BandIndex := (Σ e : Bool, Fin (D.joined.chain e).count) ⊕ (Bool ⊕ Fin D.third.count)

def bandData : D.BandIndex → M64IntrinsicLinearBandData
  | .inl ⟨e, i⟩ => .ofChain (D.joined.chain e) i
  | .inr (.inl e) => .ofPatch D.joined.patch e
  | .inr (.inr i) => .ofChain D.third i

theorem band_union : (⋃ i, (D.bandData i).band.carrier) =
    m64IntrinsicJoinedBandUnion D.joined.chain D.joined.patch ∪
      ⋃ i, (D.third.band i).carrier := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    rcases i with ⟨e, i⟩ | (e | i)
    · exact Or.inl (mem_iUnion.mpr ⟨e, Or.inl (mem_iUnion.mpr ⟨i, hi⟩)⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨e, Or.inr hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
  · rintro (hp | hp)
    · obtain ⟨e, hp⟩ := mem_iUnion.mp hp
      rcases hp with hp | hp
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
        exact mem_iUnion.mpr ⟨.inl ⟨e, i⟩, hi⟩
      · exact mem_iUnion.mpr ⟨.inr (.inl e), hp⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨.inr (.inr i), hi⟩

theorem band_subset (i : D.BandIndex) : (D.bandData i).band.carrier ⊆ D.carrier := by
  intro p hp
  have h : p ∈ ⋃ i, (D.bandData i).band.carrier := mem_iUnion.mpr ⟨i, hp⟩
  rw [D.band_union] at h
  rcases h with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem band_lower_subset
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) (i : D.BandIndex) :
    (D.bandData i).band.lowerArc ⊆ frontier U := by
  have hgamma (e : Bool) : gamma e '' Icc 0 (T e) ⊆ frontier U := by
    rw [hfront]
    cases e
    · exact subset_union_left.trans subset_union_left
    · exact subset_union_right.trans subset_union_left
  rcases i with ⟨e, i⟩ | (e | i)
  · apply ((D.joined.chain e).lower_subset i).trans
    apply Subset.trans _ (hgamma e)
    apply image_mono
    apply Icc_subset_Icc
    · cases e
      · exact (C.radius_pos false).le
      · exact (D.joined.attachment true).1.le
    · cases e
      · exact (D.joined.attachment false).2.le
      · exact sub_le_self _ (C.radius_pos true).le
  · change (D.joined.patch.band e).lowerArc ⊆ _
    rw [D.joined.patch.lower_arc]
    cases e
    · exact (image_mono (Icc_subset_Icc (D.joined.attachment false).1.le le_rfl)).trans
        (hgamma false)
    · exact (image_mono (Icc_subset_Icc le_rfl (D.joined.attachment true).2.le)).trans
        (hgamma true)
  · apply (D.third.lower_subset i).trans
    have hfull : (fun t => sigma (if D.reversed then S - t else t)) '' Icc 0 S =
        sigma '' Icc 0 S := by
      cases D.reversed
      · rfl
      · change (sigma ∘ fun t => S - t) '' Icc 0 S = _
        rw [image_comp, image_const_sub_Icc]
        simp only [sub_self, sub_zero]
    apply Subset.trans (image_mono (Icc_subset_Icc (C.radius_pos _).le
      (sub_le_self _ (C.radius_pos _).le)))
    rw [hfull, hfront]
    exact subset_union_right

end M64IntrinsicThreeArcCollar

end PoincareConjecture
