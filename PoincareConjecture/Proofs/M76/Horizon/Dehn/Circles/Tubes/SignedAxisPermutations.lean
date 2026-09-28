import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentJointSigns
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondSquareCoordinates









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)


@[ext] structure SignedAxisPermutation where
  swap : Bool
  sign : Fin 2 → Bool

namespace SignedAxisPermutation

def index (a : SignedAxisPermutation) (j : Fin 2) : Fin 2 := jointSheetIndex a.swap j

def refl : SignedAxisPermutation := ⟨false, fun _ ↦ true⟩


def trans (a b : SignedAxisPermutation) : SignedAxisPermutation :=
  ⟨Bool.xor a.swap b.swap, fun j ↦ signedTubeReindex (b.sign (a.index j)) (a.sign j)⟩

def symm (a : SignedAxisPermutation) : SignedAxisPermutation :=
  ⟨a.swap, fun j ↦ a.sign (a.index j)⟩

def coordinate (j : Fin 2) (x : P2) : ℝ := if j = 0 then x.1 else x.2

noncomputable def linear (a : SignedAxisPermutation) : P2 ≃L[ℝ] P2 :=
  (signedTubeReflection a.sign).trans
    (if a.swap then ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
      else ContinuousLinearEquiv.refl ℝ P2)

theorem linear_apply (a : SignedAxisPermutation) (x : P2) :
    a.linear x = if a.swap then
      ((if a.sign 1 then 1 else -1) * x.2, (if a.sign 0 then 1 else -1) * x.1)
    else ((if a.sign 0 then 1 else -1) * x.1, (if a.sign 1 then 1 else -1) * x.2) := by
  cases h : a.swap <;> simp [linear, h, signedTubeReflection_apply]

theorem index_rev (a : SignedAxisPermutation) (j : Fin 2) :
    a.index j.rev = (a.index j).rev := jointSheetIndex_rev a.swap j

@[simp] theorem linear_zero (a : SignedAxisPermutation) : a.linear (0, 0) = (0, 0) :=
  map_zero a.linear

theorem coordinate_linear (a : SignedAxisPermutation) (j : Fin 2) (x : P2) :
    coordinate (a.index j) (a.linear x) =
      (if a.sign j then 1 else -1) * coordinate j x := by
  cases hs : a.swap <;> fin_cases j <;>
    simp [coordinate, index, jointSheetIndex, linear_apply, hs, Fin.rev]

theorem coordinate_zero_iff (a : SignedAxisPermutation) (j : Fin 2) (x : P2) :
    coordinate (a.index j) (a.linear x) = 0 ↔ coordinate j x = 0 := by
  rw [coordinate_linear]
  cases a.sign j <;> simp

theorem side_iff (a : SignedAxisPermutation) (j : Fin 2) (b : Bool) (x : P2) :
    SignedJointCross.side b (coordinate j x) ↔
      SignedJointCross.side (signedTubeReindex (a.sign j) b)
        (coordinate (a.index j) (a.linear x)) := by
  rw [coordinate_linear]
  cases a.sign j <;> cases b <;>
    simp [SignedJointCross.side, signedTubeReindex]

theorem linear_trans_apply (a b : SignedAxisPermutation) (x : P2) :
    (a.trans b).linear x = b.linear (a.linear x) := by
  rcases a with ⟨aswap, asign⟩
  rcases b with ⟨bswap, bsign⟩
  cases aswap <;> cases bswap <;>
    cases ha0 : asign 0 <;> cases ha1 : asign 1 <;>
    cases hb0 : bsign 0 <;> cases hb1 : bsign 1 <;>
    simp [linear_apply, trans, index, jointSheetIndex, signedTubeReindex,
      ha0, ha1, hb0, hb1, Fin.rev]

theorem linear_apply_symm (a : SignedAxisPermutation) (x : P2) :
    a.linear (a.symm.linear x) = x := by
  rcases a with ⟨swap, sign⟩
  cases swap <;> cases h0 : sign 0 <;> cases h1 : sign 1 <;>
    simp [linear_apply, symm, index, jointSheetIndex, h0, h1, Fin.rev]

theorem linear_symm_apply (a : SignedAxisPermutation) (x : P2) :
    a.symm.linear (a.linear x) = x := by
  rcases a with ⟨swap, sign⟩
  cases swap <;> cases h0 : sign 0 <;> cases h1 : sign 1 <;>
    simp [linear_apply, symm, index, jointSheetIndex, h0, h1, Fin.rev]

theorem mem_diamond (a : SignedAxisPermutation) (x : P2) :
    x ∈ signedTubeDiamond ↔ a.linear x ∈ signedTubeDiamond := by
  rw [signedTubeDiamond_coordinate_iff, signedTubeDiamond_coordinate_iff]
  cases hs : a.swap <;> cases h0 : a.sign 0 <;> cases h1 : a.sign 1 <;>
    simp [linear_apply, hs, h0, h1, add_comm]

noncomputable def diamond (a : SignedAxisPermutation) :
    signedTubeDiamond ≃ₜ signedTubeDiamond :=
  a.linear.toHomeomorph.subtype (a.mem_diamond)

theorem diamond_trans_apply (a b : SignedAxisPermutation) (x : signedTubeDiamond) :
    (a.trans b).diamond x = b.diamond (a.diamond x) :=
  Subtype.ext (a.linear_trans_apply b x)

theorem diamond_apply_symm (a : SignedAxisPermutation) (x : signedTubeDiamond) :
    a.diamond (a.symm.diamond x) = x := Subtype.ext (a.linear_apply_symm x)

theorem diamond_symm_apply (a : SignedAxisPermutation) (x : signedTubeDiamond) :
    a.symm.diamond (a.diamond x) = x := Subtype.ext (a.linear_symm_apply x)

theorem diamond_isFinitePL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {G : signedTubeDiamond ≃ₜ s} (hG : G.IsFinitePL)
    (a : SignedAxisPermutation) : a.diamond.IsFinitePL := by
  obtain ⟨f, ⟨K, hK, hspace, _⟩, _⟩ := hG
  exact ⟨a.linear, ⟨K, hK, hspace,
    K.affineOnFaces_affine a.linear.toContinuousLinearMap.toContinuousAffineMap⟩,
      fun _ ↦ rfl⟩

theorem linear_corner (a : SignedAxisPermutation) (i : Fin 2) (b : Bool) :
    a.linear (signedTubeCorner i b) =
      signedTubeCorner (a.index i) (signedTubeReindex (a.sign i.rev) b) := by
  cases hs : a.swap <;> fin_cases i <;>
    cases h0 : a.sign 0 <;> cases h1 : a.sign 1 <;> cases b <;>
    norm_num [linear_apply, index, jointSheetIndex, signedTubeCorner, signedTubeReindex,
      hs, h0, h1, Fin.rev, Fin.last]

theorem linear_radius (a : SignedAxisPermutation) (i : Fin 2) (b : Bool) :
    a.linear '' signedTubeRadius i b =
      signedTubeRadius (a.index i) (signedTubeReindex (a.sign i.rev) b) := by
  have h := image_segment ℝ a.linear.toLinearMap.toAffineMap (0, 0) (signedTubeCorner i b)
  change a.linear '' segment ℝ (0, 0) (signedTubeCorner i b) =
    segment ℝ (a.linear (0, 0)) (a.linear (signedTubeCorner i b)) at h
  simpa only [signedTubeRadius, linear_zero, a.linear_corner i b] using h

def quarterLabel (a : SignedAxisPermutation) (label : Fin 2 → Bool) (j : Fin 2) : Bool :=
  signedTubeReindex (a.sign (a.index j)) (label (a.index j))

theorem mem_quarter (a : SignedAxisPermutation) (label : Fin 2 → Bool) (x : P2) :
    a.linear x ∈ signedTubeQuarter (a.quarterLabel label 0) (a.quarterLabel label 1) ↔
      x ∈ signedTubeQuarter (label 0) (label 1) := by
  rw [signedTubeQuarter_coordinate_iff, signedTubeQuarter_coordinate_iff]
  cases hs : a.swap <;>
    cases h0 : a.sign 0 <;> cases h1 : a.sign 1 <;>
    cases hb0 : label 0 <;> cases hb1 : label 1 <;>
    simp [linear_apply, quarterLabel, index, jointSheetIndex, signedTubeReindex,
      hs, h0, h1, hb0, hb1, Fin.rev, add_comm, and_left_comm]

theorem mem_sheet (a : SignedAxisPermutation) (x : signedTubeDiamond) (i : Fin 2) :
    (a.diamond x : P2) ∈ signedTubeSheet (a.index i) ↔
      (x : P2) ∈ signedTubeSheet i := by
  rw [signedTubeSheet_coordinate_iff _ (a.diamond x).property,
    signedTubeSheet_coordinate_iff _ x.property]
  exact a.coordinate_zero_iff i x

end SignedAxisPermutation

end PoincareConjecture.M76.Dehn
