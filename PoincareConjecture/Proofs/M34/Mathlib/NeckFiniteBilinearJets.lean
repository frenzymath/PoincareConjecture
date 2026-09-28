import PoincareConjecture.Proofs.M34.Mathlib.FiniteBilinearCoordinates
import PoincareConjecture.Proofs.M34.Mathlib.FiniteJetNormBounds

set_option autoImplicit false
set_option maxSynthPendingDepth 12

open scoped ContDiff BigOperators
open Poincare.Analysis.Calculus

theorem exists_piLpBilinearFromCoordinates_jet_bound
    {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {𝕜 I J E F : Type*} [NontriviallyNormedField 𝕜]
    [Fintype I] [Fintype J]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (f : E → I → J → F) (x : E),
      (∀ i j, ContDiffAt 𝕜 m (fun y => f y i j) x) →
      ∀ A : ℝ, (∀ i j, ‖iteratedFDeriv 𝕜 m (fun y => f y i j) x‖ ≤ A) →
      ‖iteratedFDeriv 𝕜 m (fun y =>
        ContinuousLinearMap.piLpBilinearFromCoordinates (p := p) (q := q) (𝕜 := 𝕜)
          (f y)) x‖ ≤ C * A := by
  classical
  let L : I × J → F →L[𝕜]
      (PiLp p fun _ : I => 𝕜) →L[𝕜] (PiLp q fun _ : J => 𝕜) →L[𝕜] F := fun ij =>
    (ContinuousLinearMap.smulRightL 𝕜 (PiLp p (fun _ : I => 𝕜))
      ((PiLp q fun _ : J => 𝕜) →L[𝕜] F) (PiLp.proj p (fun _ : I => 𝕜) ij.1)).comp
      (ContinuousLinearMap.smulRightL 𝕜 (PiLp q (fun _ : J => 𝕜)) F
        (PiLp.proj q (fun _ : J => 𝕜) ij.2))
  refine ⟨∑ ij : I × J, ‖L ij‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro m f x hs A hb
  have heq : (fun y =>
      ContinuousLinearMap.piLpBilinearFromCoordinates (p := p) (q := q) (𝕜 := 𝕜)
        (f y)) = (fun y => ∑ ij : I × J, L ij (f y ij.1 ij.2)) := by
    funext y
    rw [ContinuousLinearMap.piLpBilinearFromCoordinates_apply, Fintype.sum_prod_type]
    rfl
  rw [heq]
  calc
    _ ≤ ∑ ij : I × J, ‖iteratedFDeriv 𝕜 m (fun y => L ij (f y ij.1 ij.2)) x‖ :=
      norm_iteratedFDeriv_sum_le_of_contDiffAt Finset.univ m
        (fun ij _ => (L ij).contDiff.contDiffAt.comp x (hs ij.1 ij.2))
    _ ≤ ∑ ij : I × J, ‖L ij‖ * A := by
      apply Finset.sum_le_sum
      intro ij _
      exact ((L ij).norm_iteratedFDeriv_comp_left (hs ij.1 ij.2) (le_refl _)).trans
        (mul_le_mul_of_nonneg_left (hb ij.1 ij.2) (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm
