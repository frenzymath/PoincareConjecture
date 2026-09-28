import PoincareConjecture.Proofs.M35.Uniqueness.InitialRotationBounds
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCompactVectorHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

def rotationCutoff (j : ℕ) : ContDiffBump (0 : StandardCapSpace) where
  rIn := (j : ℝ) + 1
  rOut := (j : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def rotationCutoffSchwartz (j : ℕ) : 𝓢(StandardCapSpace, ℝ) :=
  (rotationCutoff j).hasCompactSupport.toSchwartzMap (rotationCutoff j).contDiff

def cutoffRotationField (j : ℕ) (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (x : StandardCapSpace) : StandardCapSpace := rotationCutoff j x • B x

theorem cutoffRotationField_contDiff (j : ℕ)
    (B : StandardCapSpace →L[ℝ] StandardCapSpace) :
    ContDiff ℝ ∞ (cutoffRotationField j B) :=
  (rotationCutoff j).contDiff.smul B.contDiff

theorem cutoffRotationField_eq (j : ℕ) (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    {x : StandardCapSpace} (hx : x ∈ Metric.closedBall 0 ((j : ℝ) + 1)) :
    cutoffRotationField j B x = B x := by
  simp only [cutoffRotationField, (rotationCutoff j).one_of_mem_closedBall hx, one_smul]

theorem cutoffRotationField_zero (j : ℕ) (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    {x : StandardCapSpace} (hx : x ∉ Metric.closedBall 0 ((j : ℝ) + 2)) :
    cutoffRotationField j B x = 0 := by
  have hx' : (j : ℝ) + 2 ≤ dist x 0 := (not_le.mp hx).le
  simp only [cutoffRotationField, (rotationCutoff j).zero_of_le_dist hx', zero_smul]

def rotationInitialTest (j : ℕ) (B : StandardCapSpace →L[ℝ] StandardCapSpace) (i : Fin 3) :
    supportedTests (Metric.closedBall (0 : StandardCapSpace) ((j : ℝ) + 2)) := by
  let f : StandardCapSpace → ℝ := fun x => cutoffRotationField j B x i
  have hf : ContDiff ℝ ∞ f :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp
      (cutoffRotationField_contDiff j B)
  have hfc : HasCompactSupport f :=
    (rotationCutoff j).hasCompactSupport.mul_right (f' := fun x => B x i)
  refine ⟨hfc.toSchwartzMap hf, ?_⟩
  intro x hx
  change cutoffRotationField j B x i = 0
  rw [cutoffRotationField_zero j B hx]
  rfl

def rotationInitialForm (j : ℕ) (B : StandardCapSpace →L[ℝ] StandardCapSpace) :
    PiLp 2 (fun _ : Fin 3 => dirichletForm
      (Metric.closedBall (0 : StandardCapSpace) ((j : ℝ) + 2))) :=
  WithLp.toLp 2 (fun i => intoDirichletForm _ (rotationInitialTest j B i))

theorem rotationInitialTest_value (j : ℕ) (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (i : Fin 3) :
    testValue _ (rotationInitialTest j B i) =ᵐ[volume]
        fun x => cutoffRotationField j B x i := by
  exact (rotationInitialTest j B i : 𝓢(StandardCapSpace, ℝ)).coeFn_toLp 2 volume

theorem cutoffRotationField_initial_normSq_le
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hskew : ∀ x, inner ℝ x (B x) = 0) (j : ℕ) (x : StandardCapSpace) :
    g₀.metric.inner x (cutoffRotationField j B x) (cutoffRotationField j B x) ≤
      4 * ‖B‖ ^ 2 := by
  have hχ0 : 0 ≤ rotationCutoff j x := (rotationCutoff j).nonneg
  have hχ1 : rotationCutoff j x ≤ 1 := (rotationCutoff j).le_one
  have hb := initial_linear_rotation_normSq_le P E B hskew x
  change g₀.metric.euclideanCoefficients x (rotationCutoff j x • B x)
    (rotationCutoff j x • B x) ≤ _
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hχsq : rotationCutoff j x * rotationCutoff j x ≤ 1 := by nlinarith only [hχ0, hχ1]
  calc
    _ ≤ (rotationCutoff j x * rotationCutoff j x) * (4 * ‖B‖ ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hχ0) hχ0
    _ ≤ 4 * ‖B‖ ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hχsq (by positivity : 0 ≤ 4 * ‖B‖ ^ 2)

end PoincareConjecture.M35.Uniqueness.Heat
