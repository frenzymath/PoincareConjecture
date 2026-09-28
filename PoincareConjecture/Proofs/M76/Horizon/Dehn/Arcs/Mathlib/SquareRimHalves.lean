import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimFinitePL









set_option autoImplicit false

open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1


noncomputable def squareRimHalfTime (second : Bool) (t : unitInterval) : unitInterval :=
  ⟨if second then 1 - (t : ℝ) / 2 else (t : ℝ) / 2, by
    cases second <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      constructor <;> linarith [t.property.1, t.property.2]⟩


noncomputable def squareRimHalf (second : Bool) (t : unitInterval) : V2 :=
  squareRimLoop (squareRimHalfTime second t)


def squareRimHalfCarrier (second : Bool) : Set V2 := range (squareRimHalf second)

theorem squareRimHalf_coordinates (second : Bool) (t : unitInterval) :
    squareRimHalf second t =
      if second then
        if (t : ℝ) ≤ 1 / 2 then ![-1, -1 + 4 * (t : ℝ)]
        else ![-3 + 4 * (t : ℝ), 1]
      else
        if (t : ℝ) ≤ 1 / 2 then ![-1 + 4 * (t : ℝ), -1]
        else ![1, -3 + 4 * (t : ℝ)] := by
  unfold squareRimHalf
  rw [Wall.squareRimLoop_coordinates]
  cases second <;> simp only [squareRimHalfTime, Bool.false_eq_true, if_false, if_true]
  all_goals
    split_ifs <;> ext j <;> fin_cases j <;> norm_num <;>
      linarith [t.property.1, t.property.2]

@[simp] theorem squareRimHalf_zero (second : Bool) :
    squareRimHalf second 0 = (squareRimBase : V2) := by
  rw [squareRimHalf_coordinates]
  cases second <;> norm_num [squareRimBase, squareRimVertex]

@[simp] theorem squareRimHalf_one (second : Bool) :
    squareRimHalf second 1 = (squareRimVertex 2 : V2) := by
  rw [squareRimHalf_coordinates]
  cases second <;> norm_num [squareRimVertex] <;> rfl

theorem squareRimHalf_parameter (second : Bool) (t : unitInterval) :
    (squareRimHalf second t 0 + squareRimHalf second t 1 + 2) / 4 = (t : ℝ) := by
  rw [squareRimHalf_coordinates]
  cases second <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals split_ifs <;> norm_num <;> ring

theorem squareRimHalf_injective (second : Bool) :
    Function.Injective (squareRimHalf second) := by
  intro s t h
  apply Subtype.ext
  rw [← squareRimHalf_parameter second s, ← squareRimHalf_parameter second t, h]

theorem continuous_squareRimHalf (second : Bool) : Continuous (squareRimHalf second) := by
  apply continuous_subtype_val.comp (squareRimLoop.continuous.comp _)
  apply Continuous.subtype_mk
  cases second <;> simp only [Bool.false_eq_true, if_false, if_true]
  · exact continuous_subtype_val.div_const 2
  · exact continuous_const.sub (continuous_subtype_val.div_const 2)


noncomputable def squareRimHalfChart (second : Bool) :
    I01 ≃ₜ squareRimHalfCarrier second :=
  ((continuous_squareRimHalf second).isClosedEmbedding
    (squareRimHalf_injective second)).isEmbedding.toHomeomorph

@[simp] theorem squareRimHalfChart_apply (second : Bool) (t : I01) :
    (squareRimHalfChart second t : V2) = squareRimHalf second t := rfl

theorem squareRimHalfChart_finitePL (second : Bool) :
    (squareRimHalfChart second).IsFinitePL := by
  let A : ℝ →ᴬ[ℝ] ℝ := if second then
    ContinuousAffineMap.const ℝ ℝ 1 - (1 / 2 : ℝ) • ContinuousAffineMap.id ℝ ℝ
    else (1 / 2 : ℝ) • ContinuousAffineMap.id ℝ ℝ
  obtain ⟨K, hK, hspace, _⟩ := finitePiecewiseAffineOn_squareRimParameter
  have hA : FinitePiecewiseAffineOn A I01 :=
    ⟨K, hK, hspace, K.affineOnFaces_affine A⟩
  have hmap : MapsTo A I01 I01 := by
    intro t ht
    cases second <;> change _ ≤ _ ∧ _ ≤ _ <;>
      simp only [A, Bool.false_eq_true, if_false, if_true,
        ContinuousAffineMap.coe_sub, ContinuousAffineMap.coe_smul,
        ContinuousAffineMap.coe_const, ContinuousAffineMap.coe_id,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, id_eq, Function.const_apply] <;>
      constructor <;> linarith [ht.1, ht.2]
  refine ⟨squareRimParameter ∘ A,
    finitePiecewiseAffineOn_squareRimParameter.comp hA hmap, ?_⟩
  intro t
  change squareRimHalf second t = squareRimParameter (A t)
  have heq : A t = (squareRimHalfTime second t : ℝ) := by
    cases second <;> simp [A, squareRimHalfTime] <;> ring
  rw [heq, squareRimParameter_apply]
  rfl

theorem squareRimHalfCarrier_subset (second : Bool) : squareRimHalfCarrier second ⊆ Q := by
  rintro x ⟨t, rfl⟩
  exact (squareRimLoop (squareRimHalfTime second t)).property


theorem squareRimHalfCarrier_union :
    squareRimHalfCarrier false ∪ squareRimHalfCarrier true = Q := by
  apply Subset.antisymm
  · exact union_subset (squareRimHalfCarrier_subset false) (squareRimHalfCarrier_subset true)
  · intro x hx
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hb (i : Fin 2) : -1 ≤ x i ∧ x i ≤ 1 := by
      apply abs_le.mp
      simpa only [Real.norm_eq_abs, hn] using norm_le_pi_norm x i
    have he : x 1 = -1 ∨ x 0 = 1 ∨ x 0 = -1 ∨ x 1 = 1 := by
      by_contra! he
      have hlt : ‖x‖ < 1 := (pi_norm_lt_iff (by norm_num)).mpr (by
        intro i
        rw [Real.norm_eq_abs, abs_lt]
        fin_cases i <;> constructor <;> rcases hb 0 with ⟨h00, h01⟩ <;>
          rcases hb 1 with ⟨h10, h11⟩ <;> grind)
      linarith
    let t : unitInterval := ⟨(x 0 + x 1 + 2) / 4,
      ⟨by linarith [(hb 0).1, (hb 1).1], by linarith [(hb 0).2, (hb 1).2]⟩⟩
    have hf (h : x 1 = -1 ∨ x 0 = 1) : squareRimHalf false t = x := by
      rw [squareRimHalf_coordinates]
      simp only [Bool.false_eq_true, if_false]
      rcases h with h | h <;> split_ifs <;> ext i <;> fin_cases i <;>
        norm_num [t] at * <;> linarith [(hb 0).1, (hb 0).2, (hb 1).1, (hb 1).2]
    have ht (h : x 0 = -1 ∨ x 1 = 1) : squareRimHalf true t = x := by
      rw [squareRimHalf_coordinates]
      simp only [if_true]
      rcases h with h | h <;> split_ifs <;> ext i <;> fin_cases i <;>
        norm_num [t] at * <;> linarith [(hb 0).1, (hb 0).2, (hb 1).1, (hb 1).2]
    rcases he with h | h | h | h
    · exact Or.inl ⟨t, hf (Or.inl h)⟩
    · exact Or.inl ⟨t, hf (Or.inr h)⟩
    · exact Or.inr ⟨t, ht (Or.inl h)⟩
    · exact Or.inr ⟨t, ht (Or.inr h)⟩


theorem squareRimHalfCarrier_inter :
    squareRimHalfCarrier false ∩ squareRimHalfCarrier true =
      {(squareRimBase : V2), (squareRimVertex 2 : V2)} := by
  ext x
  constructor
  · rintro ⟨⟨s, rfl⟩, t, h⟩
    have hst : s = t := by
      apply Subtype.ext
      rw [← squareRimHalf_parameter false s, ← squareRimHalf_parameter true t, h]
    subst t
    have h0 := congrFun h 0
    rw [squareRimHalf_coordinates, squareRimHalf_coordinates] at h0
    simp only [Bool.false_eq_true, if_false, if_true] at h0
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · rw [if_pos hs, if_pos hs] at h0
      change (-1 : ℝ) = -1 + 4 * (s : ℝ) at h0
      have hs0 : s = 0 := by
        apply Subtype.ext
        change (s : ℝ) = 0
        linarith
      simp [hs0]
    · rw [if_neg hs, if_neg hs] at h0
      change -3 + 4 * (s : ℝ) = (1 : ℝ) at h0
      have hs1 : s = 1 := by
        apply Subtype.ext
        change (s : ℝ) = 1
        linarith
      simp [hs1]
  · intro hx
    rcases hx with hx | hx
    · subst x
      exact ⟨⟨0, squareRimHalf_zero false⟩, ⟨0, squareRimHalf_zero true⟩⟩
    · change x = (squareRimVertex 2 : V2) at hx
      subst x
      exact ⟨⟨1, squareRimHalf_one false⟩, ⟨1, squareRimHalf_one true⟩⟩

end PoincareConjecture.M76.Dehn
