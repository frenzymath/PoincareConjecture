import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakSobolevExtension











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak EuclideanTranslationNative

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)



theorem m64WeakSobolev_localized_l2_isCompact
    {S : Set E} (hS : IsOpen S) (u : ℕ → E → ℝ)
    (hw : ∀ j, MemW1pWitness 2 (u j) S)
    {A C : ℝ} (hA : ∀ j, (∫ p in S, u j p ^ 2) ≤ A)
    (hC : ∀ j i, (∫ p in S, ((hw j).weakGrad p i) ^ 2) ≤ C)
    (phi : E → ℝ) (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ S) :
    ∃ hU : ∀ j, MemLp (fun p => phi p * u j p) 2 volume,
      IsCompact (closure (range (fun j => (hU j).toLp (fun p => phi p * u j p)))) := by
  obtain ⟨P, hP⟩ := (hc.isCompact_range hphi.continuous).isBounded.exists_norm_le
  obtain ⟨D, hD⟩ := ((hc.fderiv ℝ).isCompact_range
    (hphi.continuous_fderiv (by simp))).isBounded.exists_norm_le
  have hP0 : 0 ≤ P := (norm_nonneg (phi 0)).trans (hP _ (mem_range_self _))
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ phi 0)).trans (hD _ (mem_range_self _))
  have hb (p : E) : |phi p| ≤ P := hP _ (mem_range_self p)
  have hd (p : E) : ‖fderiv ℝ phi p‖ ≤ D := hD _ (mem_range_self p)
  let U (j : ℕ) (p : E) := phi p * u j p
  let W (j : ℕ) := (hw j).mulSmoothBoundedP (by norm_num) hS hphi hP0 hD0 hb hd
  obtain ⟨H, hH⟩ := Classical.axiomOfChoice (fun j =>
    m64WeakSobolev_extend_supported hS (W j) hc.mul_right (tsupport_mul_subset_left.trans hs))
  have hU (j : ℕ) : MemLp (U j) 2 volume := by simpa using (H j).memLp
  have hG (j : ℕ) (i : Fin d) : MemLp (fun p => (H j).weakGrad p i) 2 volume := by
    simpa using (H j).weakGrad_component_memLp i
  have hP2 (p : E) : phi p ^ 2 ≤ P ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hP0).mpr (hb p)
  have hD2 (p : E) (i : Fin d) :
      (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2 ≤ D ^ 2 := by
    have hle : ‖fderiv ℝ phi p (EuclideanSpace.single i 1)‖ ≤ D := by
      calc
        _ ≤ ‖fderiv ℝ phi p‖ := by
          simpa using (fderiv ℝ phi p).le_opNorm (EuclideanSpace.single i 1)
        _ ≤ D := hd p
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) hD0).mpr hle
  have hiU (j : ℕ) := (hw j).memLp.integrable_sq
  have hiG (j : ℕ) (i : Fin d) := ((hw j).weakGrad_component_memLp i).integrable_sq
  have hUnorm (j : ℕ) : ‖(hU j).toLp (U j)‖ ^ 2 ≤ P ^ 2 * A := by
    rw [scalar_toLp_norm_sq]
    calc
      (∫ p, U j p ^ 2) = ∫ p in S, U j p ^ 2 := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro p hp
        simp only [U, image_eq_zero_of_notMem_tsupport (fun h => hp (hs h)), zero_mul,
          zero_pow (by decide : 2 ≠ 0)]
      _ ≤ ∫ p in S, P ^ 2 * u j p ^ 2 := by
        apply integral_mono (hU j).integrable_sq.integrableOn ((hiU j).const_mul _)
        intro p
        dsimp only [U]
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (hP2 p) (sq_nonneg _)
      _ ≤ P ^ 2 * A := by rw [integral_const_mul]; gcongr; exact hA j
  have hGnorm (j : ℕ) (i : Fin d) : ‖(hG j i).toLp (fun p => (H j).weakGrad p i)‖ ^ 2 ≤
      2 * (P ^ 2 * C + D ^ 2 * A) := by
    rw [scalar_toLp_norm_sq]
    have hformula (p : E) : (H j).weakGrad p i = S.indicator
        (fun p => phi p * (hw j).weakGrad p i +
          fderiv ℝ phi p (EuclideanSpace.single i 1) * u j p) p := by
      simpa only [W, MemW1pWitness.mulSmoothBoundedP, PiLp.toLp_apply,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hH j p i
    have heq : (∫ p, ((H j).weakGrad p i) ^ 2) =
        ∫ p in S, (phi p * (hw j).weakGrad p i +
          fderiv ℝ phi p (EuclideanSpace.single i 1) * u j p) ^ 2 := by
      rw [← integral_indicator hS.measurableSet]
      apply integral_congr_ae
      filter_upwards with p
      rw [hformula]
      by_cases hp : p ∈ S <;> simp [hp]
    have hpoint (p : E) :
        (phi p * (hw j).weakGrad p i +
          fderiv ℝ phi p (EuclideanSpace.single i 1) * u j p) ^ 2 ≤
        2 * (P ^ 2 * ((hw j).weakGrad p i) ^ 2 + D ^ 2 * u j p ^ 2) := by
      nlinarith [sq_nonneg (phi p * (hw j).weakGrad p i -
        fderiv ℝ phi p (EuclideanSpace.single i 1) * u j p),
        mul_le_mul_of_nonneg_right (hP2 p) (sq_nonneg ((hw j).weakGrad p i)),
        mul_le_mul_of_nonneg_right (hD2 p i) (sq_nonneg (u j p))]
    calc
      _ ≤ ∫ p in S, 2 * (P ^ 2 * ((hw j).weakGrad p i) ^ 2 + D ^ 2 * u j p ^ 2) := by
        rw [heq]
        apply integral_mono ?_
          (((hiG j i).const_mul _ |>.add ((hiU j).const_mul _)).const_mul 2) hpoint
        simpa only [W, MemW1pWitness.mulSmoothBoundedP, PiLp.toLp_apply,
          PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
          ((W j).weakGrad_component_memLp i).integrable_sq
      _ = 2 * (P ^ 2 * (∫ p in S, ((hw j).weakGrad p i) ^ 2) +
          D ^ 2 * (∫ p in S, u j p ^ 2)) := by
        rw [integral_const_mul, integral_add ((hiG j i).const_mul _) ((hiU j).const_mul _),
          integral_const_mul, integral_const_mul]
      _ ≤ _ := by
        gcongr
        · exact hC j i
        · exact hA j
  let R := Real.sqrt (max (max (P ^ 2 * A) (2 * (P ^ 2 * C + D ^ 2 * A))) 0)
  refine ⟨hU, m64WeakSobolev_l2_isCompact U H hc ?_ hU hG (R := R)
    (Real.sqrt_nonneg _) ?_ ?_⟩
  · intro j
    exact tsupport_mul_subset_left
  · intro j
    apply Real.le_sqrt_of_sq_le
    exact (hUnorm j).trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro j i
    apply Real.le_sqrt_of_sq_le
    exact (hGnorm j i).trans ((le_max_right _ _).trans (le_max_left _ _))

end PoincareConjecture
