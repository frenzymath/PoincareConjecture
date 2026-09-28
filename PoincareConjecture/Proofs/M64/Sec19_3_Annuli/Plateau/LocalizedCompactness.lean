import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakCompactness
import PoincareConjecture.Proofs.M03.Existence.EuclideanRellichNative

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace PoincareConjecture

open EuclideanTranslationNative EuclideanMollificationNative EuclideanRellichNative

theorem m64Annulus_localized_l2_isCompact
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    {A C : ℝ} (hA : ∀ j p, ‖f j p‖ ≤ A)
    (hC : ∀ j (i : Fin 2), (∫ p in interior m64AnnulusDomain,
      (fderiv ℝ (f j) p (EuclideanSpace.single i 1)) ^ 2) ≤ C)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ interior m64AnnulusDomain) :
    ∃ hU : ∀ j, MemLp (fun p => phi p * f j p) 2 volume,
      IsCompact (closure (range (fun j => (hU j).toLp (fun p => phi p * f j p)))) := by
  let S := interior m64AnnulusDomain
  let U : ℕ → LoopPlane → ℝ := fun j p => phi p * f j p
  have hUc (j : ℕ) : HasCompactSupport (U j) := hc.mul_right
  have hUd (j : ℕ) : ContDiff ℝ 1 (U j) := hphi.mul (hf j)
  have hU (j : ℕ) : MemLp (U j) 2 volume :=
    (hUd j).continuous.memLp_of_hasCompactSupport (hUc j)
  have hcol (j : ℕ) (i : Fin 2) : MemLp
      (fun p => fderiv ℝ (U j) p (EuclideanSpace.single i 1)) 2 volume :=
    (((hUd j).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hUc j).fderiv_apply ℝ _)
  have hA0 : 0 ≤ A := (norm_nonneg (f 0 0)).trans (hA 0 0)
  have hf2 (j : ℕ) (p : LoopPlane) : (f j p) ^ 2 ≤ A ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (f j p)) hA0).mpr (hA j p)
  obtain ⟨P, hP⟩ := (hc.isCompact_range hphi.continuous).isBounded.exists_norm_le
  have hP0 : 0 ≤ P := (norm_nonneg (phi 0)).trans (hP _ (mem_range_self _))
  have hphi2 (p : LoopPlane) : (phi p) ^ 2 ≤ P ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (phi p)) hP0).mpr (hP _ (mem_range_self _))
  have hphiLp : MemLp phi 2 (volume : Measure LoopPlane) :=
    hphi.continuous.memLp_of_hasCompactSupport hc
  have hiphi : Integrable (fun p => phi p ^ 2) volume := hphiLp.integrable_sq
  have hnorm (j : ℕ) : ‖(hU j).toLp (U j)‖ ≤
      Real.sqrt (max (A ^ 2 * ∫ p, phi p ^ 2) 0) := by
    apply Real.le_sqrt_of_sq_le
    rw [scalar_toLp_norm_sq]
    apply le_trans _ (le_max_left _ _)
    calc
      (∫ p, U j p ^ 2) ≤ ∫ p, A ^ 2 * phi p ^ 2 := by
        apply integral_mono (hU j).integrable_sq (hiphi.const_mul _)
        intro p
        dsimp only [U]
        nlinarith [mul_le_mul_of_nonneg_right (hf2 j p) (sq_nonneg (phi p))]
      _ = _ := integral_const_mul _ _
  have hiF (j : ℕ) (i : Fin 2) : IntegrableOn
      (fun p => (fderiv ℝ (f j) p (EuclideanSpace.single i 1)) ^ 2) S :=
    ((((hf j).continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).continuousOn
      |>.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hphiCol (i : Fin 2) : MemLp
      (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) 2 volume :=
    ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)
  have hiPhi (i : Fin 2) : IntegrableOn
      (fun p => (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2) S :=
    (hphiCol i).integrable_sq.integrableOn
  let Q (i : Fin 2) : ℝ :=
    ∫ p in S, (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2
  have hder (j : ℕ) (i : Fin 2) :
      (∫ p, (fderiv ℝ (U j) p (EuclideanSpace.single i 1)) ^ 2) ≤
        2 * (P ^ 2 * C + A ^ 2 * Q i) := by
    have hpoint (p : LoopPlane) :
        (fderiv ℝ (U j) p (EuclideanSpace.single i 1)) ^ 2 ≤
          2 * (P ^ 2 * (fderiv ℝ (f j) p (EuclideanSpace.single i 1)) ^ 2 +
            A ^ 2 * (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2) := by
      dsimp only [U]
      rw [fderiv_fun_mul (hphi.differentiable (by simp) p) ((hf j).differentiable (by simp) p)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      nlinarith [sq_nonneg (phi p * fderiv ℝ (f j) p (EuclideanSpace.single i 1) -
        f j p * fderiv ℝ phi p (EuclideanSpace.single i 1)),
        mul_le_mul_of_nonneg_right (hphi2 p)
          (sq_nonneg (fderiv ℝ (f j) p (EuclideanSpace.single i 1))),
        mul_le_mul_of_nonneg_right (hf2 j p)
          (sq_nonneg (fderiv ℝ phi p (EuclideanSpace.single i 1)))]
    calc
      _ = ∫ p in S, (fderiv ℝ (U j) p (EuclideanSpace.single i 1)) ^ 2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro p hp
        have hpU : p ∉ tsupport (U j) := fun h => hp (hs (tsupport_mul_subset_left h))
        rw [fderiv_of_notMem_tsupport ℝ hpU]
        simp
      _ ≤ ∫ p in S, 2 * (P ^ 2 * (fderiv ℝ (f j) p (EuclideanSpace.single i 1)) ^ 2 +
          A ^ 2 * (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2) :=
        integral_mono (hcol j i).integrable_sq.integrableOn
          ((((hiF j i).const_mul _).add ((hiPhi i).const_mul _)).const_mul 2) hpoint
      _ = 2 * (P ^ 2 * (∫ p in S,
          (fderiv ℝ (f j) p (EuclideanSpace.single i 1)) ^ 2) + A ^ 2 * Q i) := by
        rw [integral_const_mul, integral_add ((hiF j i).const_mul _) ((hiPhi i).const_mul _),
          integral_const_mul, integral_const_mul]
      _ ≤ _ := by gcongr; exact hC j i
  let D := Real.sqrt (max (4 * P ^ 2 * C + 2 * A ^ 2 * (Q 0 + Q 1)) 0)
  have henergy (j : ℕ) : gradientEnergy (U j) ≤ D ^ 2 := by
    dsimp only [gradientEnergy]
    rw [Fin.sum_univ_two]
    have hle : (∫ p, (fderiv ℝ (U j) p (EuclideanSpace.single 0 1)) ^ 2) +
        (∫ p, (fderiv ℝ (U j) p (EuclideanSpace.single 1 1)) ^ 2) ≤
          4 * P ^ 2 * C + 2 * A ^ 2 * (Q 0 + Q 1) := by
      linarith [hder j 0, hder j 1]
    exact hle.trans (by dsimp [D]; rw [Real.sq_sqrt (le_max_right _ _)]; exact le_max_left _ _)
  refine ⟨hU, isCompact_closure_supported_C1 (n := 2) hc (D := D)
    (R := Real.sqrt (max (A ^ 2 * ∫ p, phi p ^ 2) 0)) (Real.sqrt_nonneg _) ?_ ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact hnorm j
  · rintro _ ⟨j, rfl⟩
    refine ⟨U j, hUd j, hU j, hcol j, ?_, rfl, henergy j⟩
    intro p hp
    dsimp only [U]
    rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]

end PoincareConjecture
