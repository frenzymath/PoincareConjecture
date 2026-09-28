import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.UpperLevel.Roots

noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

def upperSourceHeight (q : E2) : Real := 13 / 10 - (q 0)^2 - (q 1)^2 - (3 / 10) * q 0

def upperLevelSet : Set E2 := {q | ‖q‖^2 + (upperSourceHeight q)^2 = 1}

def upperArc (σ z : Real) : E2 :=
  upperAbscissa z • EuclideanSpace.single 0 1 +
    (σ * Real.sqrt (upperRadicand z)) • EuclideanSpace.single 1 1

@[simp] theorem upperArc_zero (σ z : Real) : upperArc σ z 0 = upperAbscissa z := by
  simp [upperArc]

@[simp] theorem upperArc_one (σ z : Real) : upperArc σ z 1 = σ * Real.sqrt (upperRadicand z) := by
  simp [upperArc]

theorem continuous_upperArc (σ : Real) : Continuous (upperArc σ) := by
  unfold upperArc upperRadicand upperAbscissa
  fun_prop

theorem upperArc_norm_sq {σ z : Real} (hσ : σ^2 = 1) (hz : 0 ≤ upperRadicand z) :
    ‖upperArc σ z‖^2 = 1 - z^2 := by
  rw [norm_sq_two, upperArc_zero, upperArc_one, mul_pow, hσ, one_mul, Real.sq_sqrt hz]
  dsimp [upperRadicand]
  ring

theorem upperSourceHeight_upperArc {σ z : Real} (hσ : σ^2 = 1) (hz : 0 ≤ upperRadicand z) :
    upperSourceHeight (upperArc σ z) = z := by
  have hn := upperArc_norm_sq hσ hz
  rw [norm_sq_two] at hn
  dsimp [upperSourceHeight]
  simp only [upperArc_zero] at *
  dsimp [upperAbscissa] at *
  nlinarith

theorem upperArc_mem_upperLevelSet {σ z : Real} (hσ : σ^2 = 1) (hz : 0 ≤ upperRadicand z) :
    upperArc σ z ∈ upperLevelSet := by
  change ‖upperArc σ z‖^2 + (upperSourceHeight (upperArc σ z))^2 = 1
  rw [upperArc_norm_sq hσ hz, upperSourceHeight_upperArc hσ hz]
  ring

theorem upperLevelSet_point_coordinates {q : E2} (hq : q ∈ upperLevelSet) :
    q 0 = upperAbscissa (upperSourceHeight q) ∧
      (q 1)^2 = upperRadicand (upperSourceHeight q) := by
  change ‖q‖^2 + (upperSourceHeight q)^2 = 1 at hq
  rw [norm_sq_two] at hq
  have hsource : upperSourceHeight q = 13 / 10 - (q 0)^2 - (q 1)^2 - (3 / 10) * q 0 := rfl
  have hx : q 0 = upperAbscissa (upperSourceHeight q) := by
    dsimp [upperAbscissa]
    nlinarith
  refine ⟨hx, ?_⟩
  dsimp [upperRadicand]
  rw [← hx]
  nlinarith

theorem upperLevelSet_point_eq_arc {q : E2} (hq : q ∈ upperLevelSet) :
    q = upperArc 1 (upperSourceHeight q) ∨ q = upperArc (-1) (upperSourceHeight q) := by
  obtain ⟨hx, hy⟩ := upperLevelSet_point_coordinates hq
  have hs : Real.sqrt (upperRadicand (upperSourceHeight q)) = |q 1| := by
    rw [← hy, Real.sqrt_sq_eq_abs]
  by_cases hpos : 0 ≤ q 1
  · left
    ext i
    fin_cases i
    · change q 0 = upperArc 1 (upperSourceHeight q) 0
      rw [upperArc_zero]
      exact hx
    · simp [hs, abs_of_nonneg hpos]
  · right
    ext i
    fin_cases i
    · change q 0 = upperArc (-1) (upperSourceHeight q) 0
      rw [upperArc_zero]
      exact hx
    · simp [hs, abs_of_neg (lt_of_not_ge hpos)]

theorem upperLevelSet_eq_union : upperLevelSet =
    upperArc 1 '' Icc 0 upperCutLatitude ∪ upperArc (-1) '' Icc 0 upperCutLatitude := by
  apply Subset.antisymm
  · intro q hq
    have hz : upperSourceHeight q ∈ Icc 0 upperCutLatitude :=
      (upperRadicand_nonneg_iff _).mp (by
        rw [← (upperLevelSet_point_coordinates hq).2]
        exact sq_nonneg _)
    rcases upperLevelSet_point_eq_arc hq with he | he
    · exact Or.inl ⟨upperSourceHeight q, hz, he.symm⟩
    · exact Or.inr ⟨upperSourceHeight q, hz, he.symm⟩
  · rintro q (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact upperArc_mem_upperLevelSet (by norm_num) ((upperRadicand_nonneg_iff z).mpr hz)
    · exact upperArc_mem_upperLevelSet (by norm_num) ((upperRadicand_nonneg_iff z).mpr hz)

theorem isCompact_upperLevelSet : IsCompact upperLevelSet := by
  rw [upperLevelSet_eq_union]
  exact (isCompact_Icc.image (continuous_upperArc 1)).union
    (isCompact_Icc.image (continuous_upperArc (-1)))

theorem isConnected_upperLevelSet : IsConnected upperLevelSet := by
  rw [upperLevelSet_eq_union]
  apply ((isConnected_Icc upperCutLatitude_pos.le).image _
    (continuous_upperArc 1).continuousOn).union ?_
      ((isConnected_Icc upperCutLatitude_pos.le).image _ (continuous_upperArc (-1)).continuousOn)
  refine ⟨upperArc 1 0, ⟨0, ⟨le_rfl, upperCutLatitude_pos.le⟩, rfl⟩,
    ⟨0, ⟨le_rfl, upperCutLatitude_pos.le⟩, ?_⟩⟩
  simp [upperArc]

end Poincare.Manifold.Schoenflies.Saddle.Nested
