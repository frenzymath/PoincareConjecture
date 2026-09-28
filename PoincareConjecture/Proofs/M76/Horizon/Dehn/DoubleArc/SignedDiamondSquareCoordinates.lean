import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondReflection
import PoincareConjecture.Proofs.M76.Mathlib.TriangleDiskRegions
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalCrossingResolution
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem signedTubeQuarter_coordinate_iff (eps delta : Bool) (x : P2) :
    x ∈ signedTubeQuarter eps delta ↔
      0 ≤ (if eps then x.1 else -x.1) ∧ 0 ≤ (if delta then x.2 else -x.2) ∧
        (if eps then x.1 else -x.1) + (if delta then x.2 else -x.2) ≤ 1 := by
  have hpositive (y : P2) : y ∈ signedTubeQuarter true true ↔
      0 ≤ y.1 ∧ 0 ≤ y.2 ∧ y.1 + y.2 ≤ 1 := by
    simpa [signedTubeQuarter, signedTubeCorner, TriangleDiskModel.rightTriangle] using
      TriangleDiskModel.mem_right_region_iff y
  have h := signedTubeReflection_mem_quarter ![eps, delta] eps delta x
  cases eps <;> cases delta <;>
    simp only [signedTubeReindex, Matrix.cons_val_zero, Matrix.cons_val_one,
      Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
    rw [← h, hpositive] <;> simp [signedTubeReflection_apply]

theorem signedTubeDiamond_coordinate_iff (x : P2) :
    x ∈ signedTubeDiamond ↔ |x.1| + |x.2| ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨eps, heps⟩ := mem_iUnion.mp hx
    obtain ⟨delta, hx⟩ := mem_iUnion.mp heps
    have h := (signedTubeQuarter_coordinate_iff eps delta x).mp hx
    cases eps <;> cases delta <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
    · rw [abs_of_nonpos (by linarith [h.1]), abs_of_nonpos (by linarith [h.2.1])]
      exact h.2.2
    · rw [abs_of_nonpos (by linarith [h.1]), abs_of_nonneg h.2.1]
      exact h.2.2
    · rw [abs_of_nonneg h.1, abs_of_nonpos (by linarith [h.2.1])]
      exact h.2.2
    · rw [abs_of_nonneg h.1, abs_of_nonneg h.2.1]
      exact h.2.2
  · intro hx
    by_cases hx0 : 0 ≤ x.1
    · by_cases hx1 : 0 ≤ x.2
      · refine mem_iUnion.mpr ⟨true, mem_iUnion.mpr ⟨true,
          (signedTubeQuarter_coordinate_iff true true x).mpr ?_⟩⟩
        simp only [↓reduceIte]
        exact ⟨hx0, hx1, by simpa only [abs_of_nonneg hx0, abs_of_nonneg hx1] using hx⟩
      · have hn := (lt_of_not_ge hx1).le
        refine mem_iUnion.mpr ⟨true, mem_iUnion.mpr ⟨false,
          (signedTubeQuarter_coordinate_iff true false x).mpr ?_⟩⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hx0, by linarith, by simpa only [abs_of_nonneg hx0, abs_of_nonpos hn] using hx⟩
    · have hn0 := (lt_of_not_ge hx0).le
      by_cases hx1 : 0 ≤ x.2
      · refine mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨true,
          (signedTubeQuarter_coordinate_iff false true x).mpr ?_⟩⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨by linarith, hx1, by simpa only [abs_of_nonpos hn0, abs_of_nonneg hx1] using hx⟩
      · have hn1 := (lt_of_not_ge hx1).le
        refine mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨false,
          (signedTubeQuarter_coordinate_iff false false x).mpr ?_⟩⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨by linarith, by linarith, by simpa only [abs_of_nonpos hn0, abs_of_nonpos hn1] using hx⟩

noncomputable def signedSquareToDiamond : P2 ≃L[ℝ] P2 :=
  ({ toFun := fun x => ((x.1 - x.2) / 2, (x.1 + x.2) / 2)
     invFun := fun y => (y.2 + y.1, y.2 - y.1)
     left_inv := by intro x; ext <;> dsimp <;> ring
     right_inv := by intro x; ext <;> dsimp <;> ring
     map_add' := by intro x y; ext <;> dsimp <;> ring
     map_smul' := by intro r x; ext <;> dsimp <;> ring } : P2 ≃ₗ[ℝ] P2).toContinuousLinearEquiv

theorem signedSquareToDiamond_apply (x : P2) :
    signedSquareToDiamond x = ((x.1 - x.2) / 2, (x.1 + x.2) / 2) := rfl

theorem signedSquareToDiamond_mem (x : P2) :
    signedSquareToDiamond x ∈ signedTubeDiamond ↔ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
  rw [signedTubeDiamond_coordinate_iff, signedSquareToDiamond_apply]
  change |(x.1 - x.2) / 2| + |(x.1 + x.2) / 2| ≤ 1 ↔
    (-1 ≤ x.1 ∧ x.1 ≤ 1) ∧ (-1 ≤ x.2 ∧ x.2 ≤ 1)
  rw [abs_div, abs_div]
  norm_num
  constructor
  · intro hx
    have h0 := neg_abs_le (x.1 - x.2)
    have h1 := le_abs_self (x.1 - x.2)
    have h2 := neg_abs_le (x.1 + x.2)
    have h3 := le_abs_self (x.1 + x.2)
    constructor <;> constructor <;> linarith
  · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
    by_cases ha : 0 ≤ x.1 - x.2 <;> by_cases hb : 0 ≤ x.1 + x.2
    · rw [abs_of_nonneg ha, abs_of_nonneg hb]
      linarith
    · rw [abs_of_nonneg ha, abs_of_nonpos (lt_of_not_ge hb).le]
      linarith
    · rw [abs_of_nonpos (lt_of_not_ge ha).le, abs_of_nonneg hb]
      linarith
    · rw [abs_of_nonpos (lt_of_not_ge ha).le, abs_of_nonpos (lt_of_not_ge hb).le]
      linarith

theorem signedTubeSheet_coordinate_iff (x : P2) (hx : x ∈ signedTubeDiamond) (i : Fin 2) :
    x ∈ signedTubeSheet i ↔ (if i = 0 then x.1 else x.2) = 0 := by
  have hbound := (signedTubeDiamond_coordinate_iff x).mp hx
  fin_cases i
  · change (x ∈ signedTubeRadius 0 false ∨ x ∈ signedTubeRadius 0 true) ↔ x.1 = 0
    constructor
    · rintro (hx | hx)
      all_goals
        obtain ⟨a, b, ha, hb, hab, hval⟩ := hx
        have hh := congrArg Prod.fst hval
        simpa [signedTubeCorner] using hh.symm
    · intro hz
      have hr : |x.2| ≤ 1 := by simpa only [hz, abs_zero, zero_add] using hbound
      by_cases hn : 0 ≤ x.2
      · refine Or.inr ⟨1 - x.2, x.2, by linarith [(abs_le.mp hr).2], hn, by ring, ?_⟩
        ext <;> simp [signedTubeCorner, hz]
      · refine Or.inl ⟨1 + x.2, -x.2, by linarith [(abs_le.mp hr).1], by linarith, by ring, ?_⟩
        ext <;> simp [signedTubeCorner, hz]
  · change (x ∈ signedTubeRadius 1 false ∨ x ∈ signedTubeRadius 1 true) ↔ x.2 = 0
    constructor
    · rintro (hx | hx)
      all_goals
        obtain ⟨a, b, ha, hb, hab, hval⟩ := hx
        have hh := congrArg Prod.snd hval
        simpa [signedTubeCorner] using hh.symm
    · intro hz
      have hr : |x.1| ≤ 1 := by simpa only [hz, abs_zero, add_zero] using hbound
      by_cases hn : 0 ≤ x.1
      · refine Or.inr ⟨1 - x.1, x.1, by linarith [(abs_le.mp hr).2], hn, by ring, ?_⟩
        ext <;> simp [signedTubeCorner, hz]
      · refine Or.inl ⟨1 + x.1, -x.1, by linarith [(abs_le.mp hr).1], by linarith, by ring, ?_⟩
        ext <;> simp [signedTubeCorner, hz]

theorem signedSquareToDiamond_sheet (x : P2)
    (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) (i : Fin 2) :
    signedSquareToDiamond x ∈ signedTubeSheet i ↔
      x.2 = if i = 0 then x.1 else -x.1 := by
  rw [signedTubeSheet_coordinate_iff _ ((signedSquareToDiamond_mem x).mpr hx)]
  fin_cases i <;> norm_num [signedSquareToDiamond_apply] <;>
    constructor <;> intro h <;> linarith

local notation "C3" => (P2 × ℝ)

noncomputable def signedSquarePrismCoordinates : C3 ≃L[ℝ] C3 :=
  signedSquareToDiamond.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem signedSquarePrismCoordinates_mem (x : C3) :
    x ∈ PolygonalCrossingResolution.tube ↔
      signedSquarePrismCoordinates x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) 1 := by
  exact ((signedSquareToDiamond_mem x.1).symm).and Iff.rfl

noncomputable def signedSquareTubeCoordinates :
    PolygonalCrossingResolution.tube ≃ₜ ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) :=
  signedSquarePrismCoordinates.toHomeomorph.subtype signedSquarePrismCoordinates_mem

theorem signedSquareTubeCoordinates_isFinitePL : signedSquareTubeCoordinates.IsFinitePL := by
  have hunit := isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  have htime := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hball := (hunit.prod hunit).prod htime
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  exact ⟨signedSquarePrismCoordinates, ⟨K, hK, hKs,
    K.affineOnFaces_affine signedSquarePrismCoordinates.toContinuousLinearMap.toContinuousAffineMap⟩,
    fun _ => rfl⟩

theorem signedSquareTubeCoordinates_axis (t : Icc (0 : ℝ) 1) :
    (signedSquareTubeCoordinates ⟨((0, 0), t), by
      exact ⟨⟨by norm_num, by norm_num⟩, t.property⟩⟩ : C3) = ((0, 0), (t : ℝ)) := by
  change (((0 - 0) / 2, (0 + 0) / 2), (t : ℝ)) = _
  norm_num

end PoincareConjecture.M76.Dehn
