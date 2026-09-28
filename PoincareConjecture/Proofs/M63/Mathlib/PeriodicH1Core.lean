import PoincareConjecture.Proofs.M63.Mathlib.PeriodicFourierCoordinates

set_option autoImplicit false

open AddCircle Set
open scoped ENNReal

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

noncomputable def periodicC1Core : Submodule ℂ (lp (fun _ : ℤ => ℂ) 2) where
  carrier := {u | ∃ g : C(AddCircle L, ℂ), ∀ x : ℝ, HasDerivAt
    (fun y : ℝ => periodicSobolevJet (L := L) 0 0 (by omega) u (y : AddCircle L))
    (g (x : AddCircle L)) x}
  zero_mem' := by
    refine ⟨0, fun x => ?_⟩
    simpa only [map_zero, ContinuousMap.zero_apply] using hasDerivAt_const x (0 : ℂ)
  add_mem' := by
    rintro u v ⟨g, hg⟩ ⟨h, hh⟩
    refine ⟨g + h, fun x => ?_⟩
    simpa only [map_add, ContinuousMap.add_apply] using (hg x).fun_add (hh x)
  smul_mem' := by
    rintro c u ⟨g, hg⟩
    refine ⟨c • g, fun x => ?_⟩
    simpa only [map_smul, ContinuousMap.smul_apply] using (hg x).fun_const_smul c

theorem periodicH1Decoder_single (n : ℤ) (c : ℂ) :
    periodicSobolevJet (L := L) 0 0 (by omega) (lp.single 2 n c) =
      (c / (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ)) • fourier n ∧
    ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => periodicSobolevJet (L := L) 0 0 (by omega) (lp.single 2 n c) (y : AddCircle L))
      ((Complex.I * ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ)) *
        (c / (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ)) *
          fourier n (x : AddCircle L)) x := by
  classical
  have hs := weightedFourier_hasSum (L := L)
    ⟨periodicSobolevMoment L 0 0, (periodicSobolevMoment_bound (by omega : 0 ≤ 0)).2⟩
    (lp.single 2 n c)
  have hterm (m : ℤ) :
      (periodicSobolevMoment L 0 0 m * (lp.single 2 n c : lp (fun _ : ℤ => ℂ) 2) m) •
        (fourier m : C(AddCircle L, ℂ)) =
      if m = n then
        (c / (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ)) • fourier n else 0 := by
    by_cases hm : m = n
    · subst m
      simp only [lp.single_apply_self, periodicSobolevMoment, pow_zero, zero_add, pow_one]
      congr 1
      ring
    · simp only [lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n c hm,
        mul_zero, zero_smul, if_neg hm]
  change HasSum (fun m : ℤ =>
    (periodicSobolevMoment L 0 0 m * (lp.single 2 n c : lp (fun _ : ℤ => ℂ) 2) m) • fourier m)
      (periodicSobolevJet (L := L) 0 0 (by omega) (lp.single 2 n c)) at hs
  simp_rw [hterm] at hs
  have heq := hs.unique (hasSum_ite_eq n
    ((c / (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ)) • fourier n))
  refine ⟨heq, fun x => ?_⟩
  rw [heq]
  have hd := (hasDerivAt_fourier L n x).fun_const_smul
    (c / (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ))
  apply hd.congr_deriv
  simp only [smul_eq_mul]
  push_cast
  ring

theorem dense_periodicC1Core :
    Dense (periodicC1Core (L := L) : Set (lp (fun _ : ℤ => ℂ) 2)) := by
  have hsingle (n : ℤ) (c : ℂ) : lp.single 2 n c ∈ periodicC1Core (L := L) := by
    refine ⟨((Complex.I * ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ)) *
      (c / (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ))) • fourier n, ?_⟩
    exact (periodicH1Decoder_single n c).2
  intro u
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u)
  apply Filter.Eventually.of_forall
  intro s
  exact subset_closure ((periodicC1Core (L := L)).sum_mem (fun n _ => hsingle n (u n)))

end PoincareConjecture.M63
