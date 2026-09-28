import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Roots
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LowerCaps



noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)


def levelSet : Set E2 := {q | polynomial (3 / 10) (vector (q 0) (q 1) 1) = 1}


def sourceHeight (q : E2) : Real := 1 - (q 0)^2 - (q 1)^2 - (3 / 10) * q 0


def levelArc (σ z : Real) : E2 :=
  levelAbscissa z • EuclideanSpace.single 0 1 +
    (σ * Real.sqrt (levelRadicand z)) • EuclideanSpace.single 1 1

@[simp] theorem levelArc_zero (σ z : Real) : levelArc σ z 0 = levelAbscissa z := by
  simp [levelArc]

@[simp] theorem levelArc_one (σ z : Real) :
    levelArc σ z 1 = σ * Real.sqrt (levelRadicand z) := by
  simp [levelArc]

theorem continuous_levelArc (σ : Real) : Continuous (levelArc σ) := by
  unfold levelArc levelRadicand levelAbscissa
  fun_prop

theorem levelArc_eq_of_radicand_zero {z : Real} (hz : levelRadicand z = 0)
    (σ τ : Real) : levelArc σ z = levelArc τ z := by
  simp [levelArc, hz]

theorem levelArc_norm_sq {σ z : Real} (hσ : σ^2 = 1) (hz : 0 ≤ levelRadicand z) :
    ‖levelArc σ z‖^2 = 1 - z^2 := by
  rw [norm_sq_two, levelArc_zero, levelArc_one, mul_pow, hσ, one_mul,
    Real.sq_sqrt hz]
  dsimp [levelRadicand]
  ring

theorem sourceHeight_levelArc {σ z : Real} (hσ : σ^2 = 1)
    (hz : 0 ≤ levelRadicand z) : sourceHeight (levelArc σ z) = z := by
  have hn := levelArc_norm_sq hσ hz
  rw [norm_sq_two] at hn
  dsimp [sourceHeight]
  simp only [levelArc_zero] at *
  dsimp [levelAbscissa] at *
  nlinarith

theorem mem_levelSet_iff (q : E2) :
    q ∈ levelSet ↔ ‖q‖^2 + (sourceHeight q)^2 = 1 := by
  change (q 0)^2 + (q 1)^2 + (1 - ((q 0)^2 + (q 1)^2 + (3 / 10) * q 0))^2 = 1 ↔ _
  have he : 1 - ((q 0)^2 + (q 1)^2 + (3 / 10) * q 0) = sourceHeight q := by
    dsimp [sourceHeight]
    ring
  rw [he, norm_sq_two]

theorem levelArc_mem_levelSet {σ z : Real} (hσ : σ^2 = 1)
    (hz : 0 ≤ levelRadicand z) : levelArc σ z ∈ levelSet := by
  rw [mem_levelSet_iff, levelArc_norm_sq hσ hz, sourceHeight_levelArc hσ hz]
  ring


theorem levelSet_point_coordinates {q : E2} (hq : q ∈ levelSet) :
    q 0 = levelAbscissa (sourceHeight q) ∧
      (q 1)^2 = levelRadicand (sourceHeight q) := by
  have he := (mem_levelSet_iff q).mp hq
  rw [norm_sq_two] at he
  have hsource : sourceHeight q = 1 - (q 0)^2 - (q 1)^2 - (3 / 10) * q 0 := rfl
  have hx : q 0 = levelAbscissa (sourceHeight q) := by
    dsimp [levelAbscissa]
    nlinarith
  refine ⟨hx, ?_⟩
  dsimp [levelRadicand]
  rw [← hx]
  nlinarith

theorem levelSet_point_eq_arc {q : E2} (hq : q ∈ levelSet) :
    q = levelArc 1 (sourceHeight q) ∨ q = levelArc (-1) (sourceHeight q) := by
  obtain ⟨hx, hy⟩ := levelSet_point_coordinates hq
  have hs : Real.sqrt (levelRadicand (sourceHeight q)) = |q 1| := by
    rw [← hy, Real.sqrt_sq_eq_abs]
  by_cases hpos : 0 ≤ q 1
  · left
    ext i
    fin_cases i
    · change q 0 = levelArc 1 (sourceHeight q) 0
      rw [levelArc_zero]
      exact hx
    · simp [hs, abs_of_nonneg hpos]
  · right
    ext i
    fin_cases i
    · change q 0 = levelArc (-1) (sourceHeight q) 0
      rw [levelArc_zero]
      exact hx
    · simp [hs, abs_of_neg (lt_of_not_ge hpos)]

def outerOval : Set E2 :=
  levelArc 1 '' Icc lowerRoot (3 / 5) ∪ levelArc (-1) '' Icc lowerRoot (3 / 5)

def innerOval : Set E2 :=
  levelArc 1 '' Icc upperRoot 1 ∪ levelArc (-1) '' Icc upperRoot 1


theorem levelSet_eq_outerOval_union_innerOval : levelSet = outerOval ∪ innerOval := by
  apply Subset.antisymm
  · intro q hq
    have hrad : 0 ≤ levelRadicand (sourceHeight q) := by
      rw [← (levelSet_point_coordinates hq).2]
      exact sq_nonneg _
    rcases (levelRadicand_nonneg_iff _).mp hrad with ho | hi
    · left
      rcases levelSet_point_eq_arc hq with he | he
      · exact Or.inl ⟨sourceHeight q, ho, he.symm⟩
      · exact Or.inr ⟨sourceHeight q, ho, he.symm⟩
    · right
      rcases levelSet_point_eq_arc hq with he | he
      · exact Or.inl ⟨sourceHeight q, hi, he.symm⟩
      · exact Or.inr ⟨sourceHeight q, hi, he.symm⟩
  · rintro q ((⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) | (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩))
    · exact levelArc_mem_levelSet (by norm_num) ((levelRadicand_nonneg_iff z).mpr (Or.inl hz))
    · exact levelArc_mem_levelSet (by norm_num) ((levelRadicand_nonneg_iff z).mpr (Or.inl hz))
    · exact levelArc_mem_levelSet (by norm_num) ((levelRadicand_nonneg_iff z).mpr (Or.inr hz))
    · exact levelArc_mem_levelSet (by norm_num) ((levelRadicand_nonneg_iff z).mpr (Or.inr hz))

end Poincare.Manifold.Schoenflies.Saddle.Nested
