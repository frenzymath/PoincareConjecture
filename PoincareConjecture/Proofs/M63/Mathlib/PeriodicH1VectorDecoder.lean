import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Core

set_option autoImplicit false

open AddCircle

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

noncomputable def periodicH1VectorDecoder (ι : Type*) [Fintype ι] :
    (ι → lp (fun _ : ℤ => ℂ) 2) →L[ℂ] C(AddCircle L, ι → ℂ) := by
  let D := periodicSobolevJet (L := L) 0 0 (by omega)
  let A : (ι → lp (fun _ : ℤ => ℂ) 2) →ₗ[ℂ] C(AddCircle L, ι → ℂ) :=
    { toFun := fun u => ⟨fun x i => D (u i) x,
        continuous_pi (fun i => (D (u i)).continuous)⟩
      map_add' := by
        intro u v
        ext x i
        exact congrArg (fun f : C(AddCircle L, ℂ) => f x) (D.map_add (u i) (v i))
      map_smul' := by
        intro c u
        ext x i
        exact congrArg (fun f : C(AddCircle L, ℂ) => f x) (D.map_smul c (u i)) }
  let d := ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
    memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖
  apply A.mkContinuous d
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  change ‖D (u i) x‖ ≤ d * ‖u‖
  exact ((D (u i)).norm_coe_le_norm x).trans
    ((norm_periodicSobolevJet_le 0 0 (by omega) (u i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (norm_nonneg _)))

theorem norm_periodicH1VectorDecoder_le {ι : Type*} [Fintype ι]
    (u : ι → lp (fun _ : ℤ => ℂ) 2) :
    ‖periodicH1VectorDecoder (L := L) ι u‖ ≤
      ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
        memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  change ‖periodicSobolevJet (L := L) 0 0 (by omega) (u i) x‖ ≤ _
  exact ((periodicSobolevJet (L := L) 0 0 (by omega) (u i)).norm_coe_le_norm x).trans
    ((norm_periodicSobolevJet_le 0 0 (by omega) (u i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (norm_nonneg _)))

end PoincareConjecture.M63
