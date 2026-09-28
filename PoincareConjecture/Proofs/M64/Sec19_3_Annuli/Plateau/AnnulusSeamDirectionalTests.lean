import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamReplacementTests
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.NonnegativeApproximation












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Convolution NNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak
  Poincare.Analysis.Sobolev.DifferenceQuotient



theorem m64WeakPartial_compact_directional_test
    {u W psi Z : LoopPlane → ℝ} {i : Fin 2}
    (hu : MemLp u 2 volume) (hW : MemLp W 2 volume)
    (hw : HasWeakPartialDeriv i W u univ)
    (hp : MemLp psi 2 volume) (hZ : MemLp Z 2 volume)
    (hpsi : HasWeakPartialDeriv i Z psi univ) (hc : HasCompactSupport psi) :
    (∫ p, u p * Z p) = -(∫ p, W p * psi p) := by
  let r := fun j : ℕ => 1 / (j + 1 : ℝ)
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hz : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let f := fun j => mollifyEps (hr j) psi
  have hf (j : ℕ) : ContDiff ℝ ∞ (f j) :=
    mollifyEps_contDiff (hr j) (hp.locallyIntegrable (by norm_num))
  have hfc (j : ℕ) : HasCompactSupport (f j) :=
    HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      (mollifierEps_compactSupport (hr j)) hc
  have hfl (j : ℕ) : MemLp (f j) 2 volume :=
    (hf j).continuous.memLp_of_hasCompactSupport (hfc j)
  have hDl (j : ℕ) : MemLp (fun p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)) 2 volume :=
    (((hf j).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hfc j).fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hval := tendsto_eLpNorm_mollifyEps_sub hr hz (by norm_num : (1 : ENNReal) ≤ 2)
    (by norm_num : (2 : ENNReal) ≠ ⊤) hp
  have hder := tendsto_eLpNorm_mollifyEps_partial_sub hr hz
    (by norm_num : (1 : ENNReal) ≤ 2) (by norm_num : (2 : ENNReal) ≠ ⊤)
    (hp.locallyIntegrable (by norm_num)) hZ hpsi
  have hl := m64L2_pairing_tendsto_of_eLpNorm hDl hZ hu hder
  have hright := (m64L2_pairing_tendsto_of_eLpNorm hfl hp hW hval).neg
  apply tendsto_nhds_unique hl
  apply hright.congr'
  filter_upwards [] with j
  simpa only [Measure.restrict_univ] using (hw (f j) (hf j) (hfc j) (subset_univ _)).symm



theorem m64WeakColumns_compact_directional_test
    {m : ℕ} {u W : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {psi Z : LoopPlane → ℝ} {i : Fin 2}
    (hu : MemLp u 2 volume) (hW : MemLp W 2 volume)
    (hw : ∀ b, HasWeakPartialDeriv i (fun p => W p b) (fun p => u p b) univ)
    (hp : MemLp psi 2 volume) (hZ : MemLp Z 2 volume)
    (hpsi : HasWeakPartialDeriv i Z psi univ) (hc : HasCompactSupport psi) :
    (∫ p, psi p • W p) + (∫ p, Z p • u p) = 0 := by
  ext b
  let L := EuclideanSpace.proj (𝕜 := ℝ) b
  have h := m64WeakPartial_compact_directional_test (L.comp_memLp' hu) (L.comp_memLp' hW)
    (hw b) hp hZ hpsi hc
  change L ((∫ p, psi p • W p) + ∫ p, Z p • u p) = L 0
  rw [map_add, map_zero,
    ← L.integral_comp_comm (m64L2_test_integrable hW hp),
    ← L.integral_comp_comm (m64L2_test_integrable hu hZ)]
  simp only [L, EuclideanSpace.coe_proj, Function.comp_def, PiLp.smul_apply,
    smul_eq_mul, mul_comm] at h ⊢
  linarith



theorem m64MatchingGreen_compact_directional
    {m : ℕ} {K : Set LoopPlane} (hK : MeasurableSet K)
    (u0 u1 W0 W1 : LoopPlane → EuclideanSpace ℝ (Fin m)) {i : Fin 2}
    (hu0 : MemLp u0 2 (volume.restrict K)) (hu1 : MemLp u1 2 (volume.restrict K))
    (hW0 : MemLp W0 2 (volume.restrict K)) (hW1 : MemLp W1 2 (volume.restrict K))
    (hgreen : ∀ (phi : LoopPlane → ℝ) (L : ℝ≥0), LipschitzWith L phi → HasCompactSupport phi →
      (∫ p in K, phi p • W1 p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u1 p) =
      (∫ p in K, phi p • W0 p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u0 p))
    {psi Z : LoopPlane → ℝ} (hp : MemLp psi 2 volume) (hZ : MemLp Z 2 volume)
    (hpsi : HasWeakPartialDeriv i Z psi univ) (hc : HasCompactSupport psi) :
    (∫ p in K, psi p • W1 p) + (∫ p in K, Z p • u1 p) =
      (∫ p in K, psi p • W0 p) + (∫ p in K, Z p • u0 p) := by
  let U := K.indicator (u1 - u0)
  let W := K.indicator (W1 - W0)
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hK).mpr (hu1.sub hu0)
  have hW : MemLp W 2 volume := (memLp_indicator_iff_restrict hK).mpr (hW1.sub hW0)
  have hweak (b : Fin m) : HasWeakPartialDeriv i (fun p => W p b) (fun p => U p b) univ := by
    intro phi hphi hphic _
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hphic hphi (by simp)
    have hphiM : MemLp phi 2 volume := hphi.continuous.memLp_of_hasCompactSupport hphic
    have hdM := m64CompactLipschitz_fderiv_memLp hL hphic i
    have hpK := hphiM.mono_measure (Measure.restrict_le_self (s := K))
    have hdK := hdM.mono_measure (Measure.restrict_le_self (s := K))
    have hh : (∫ p, phi p • W p) +
        (∫ p, fderiv ℝ phi p (EuclideanSpace.single i 1) • U p) = 0 := by
      rw [m64Integral_smul_indicator hK, m64Integral_smul_indicator hK]
      simp only [Pi.sub_apply, smul_sub]
      rw [integral_sub (m64L2_test_integrable hW1 hpK) (m64L2_test_integrable hW0 hpK),
        integral_sub (m64L2_test_integrable hu1 hdK) (m64L2_test_integrable hu0 hdK)]
      calc
        _ = ((∫ p in K, phi p • W1 p) +
            ∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u1 p) -
            ((∫ p in K, phi p • W0 p) +
            ∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u0 p) := by abel
        _ = 0 := sub_eq_zero.mpr (hgreen phi L hL hphic)
    let P := EuclideanSpace.proj (𝕜 := ℝ) b
    have hs := congrArg P hh
    rw [map_add, map_zero,
      ← P.integral_comp_comm (m64L2_test_integrable hW hphiM),
      ← P.integral_comp_comm (m64L2_test_integrable hU hdM)] at hs
    simp only [P, EuclideanSpace.coe_proj, PiLp.smul_apply, smul_eq_mul, mul_comm,
      Measure.restrict_univ] at hs ⊢
    linarith
  have h := m64WeakColumns_compact_directional_test hU hW hweak hp hZ hpsi hc
  rw [m64Integral_smul_indicator hK, m64Integral_smul_indicator hK] at h
  have hpK := hp.mono_measure (Measure.restrict_le_self (s := K))
  have hdK := hZ.mono_measure (Measure.restrict_le_self (s := K))
  simp only [Pi.sub_apply, smul_sub] at h
  rw [integral_sub (m64L2_test_integrable hW1 hpK) (m64L2_test_integrable hW0 hpK),
    integral_sub (m64L2_test_integrable hu1 hdK) (m64L2_test_integrable hu0 hdK)] at h
  apply sub_eq_zero.mp
  calc
    _ = ((∫ p in K, psi p • W1 p) - ∫ p in K, psi p • W0 p) +
        ((∫ p in K, Z p • u1 p) - ∫ p in K, Z p • u0 p) := by abel
    _ = 0 := h

end PoincareConjecture
