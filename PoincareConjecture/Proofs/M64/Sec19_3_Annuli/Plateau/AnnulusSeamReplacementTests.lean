import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamSobolevTests

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

theorem m64Integral_smul_indicator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set LoopPlane} (hK : MeasurableSet K)
    (phi : LoopPlane → ℝ) (f : LoopPlane → E) :
    (∫ p, phi p • K.indicator f p) = ∫ p in K, phi p • f p := by
  rw [← integral_indicator hK]
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hp : p ∈ K
  · simp only [indicator_of_mem hp]
  · simp only [indicator_of_notMem hp, smul_zero]

theorem m64ZeroGreen_indicator_weak_partial
    {m : ℕ} {K : Set LoopPlane} (hK : MeasurableSet K)
    {u W : LoopPlane → EuclideanSpace ℝ (Fin m)} {i : Fin 2}
    (hu : MemLp u 2 (volume.restrict K)) (hW : MemLp W 2 (volume.restrict K))
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in K, phi p • W p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u p) = 0)
    (b : Fin m) :
    HasWeakPartialDeriv i (fun p => K.indicator W p b) (fun p => K.indicator u p b) univ := by
  intro phi hp hc _
  have huE := (memLp_indicator_iff_restrict hK).mpr hu
  have hWE := (memLp_indicator_iff_restrict hK).mpr hW
  have hpM : MemLp phi 2 volume := hp.continuous.memLp_of_hasCompactSupport hc
  have hdM : MemLp (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) 2 volume :=
    (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _))
  have h : (∫ p, phi p • K.indicator W p) +
      (∫ p, fderiv ℝ phi p (EuclideanSpace.single i 1) • K.indicator u p) = 0 := by
    rw [m64Integral_smul_indicator hK, m64Integral_smul_indicator hK]
    exact hgreen phi (hp.of_le (by simp))
  let L := EuclideanSpace.proj (𝕜 := ℝ) b
  have hs := congrArg L h
  rw [map_add, map_zero,
    ← L.integral_comp_comm (m64L2_test_integrable hWE hpM),
    ← L.integral_comp_comm (m64L2_test_integrable huE hdM)] at hs
  simp only [L, EuclideanSpace.coe_proj, PiLp.smul_apply, smul_eq_mul, mul_comm,
    Measure.restrict_univ] at hs ⊢
  linarith

theorem m64ZeroGreen_compact_lipschitz
    {m : ℕ} {K : Set LoopPlane} (hK : MeasurableSet K)
    {u W : LoopPlane → EuclideanSpace ℝ (Fin m)} {i : Fin 2}
    (hu : MemLp u 2 (volume.restrict K)) (hW : MemLp W 2 (volume.restrict K))
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in K, phi p • W p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u p) = 0)
    {psi : LoopPlane → ℝ} {L : ℝ≥0} (hp : LipschitzWith L psi) (hc : HasCompactSupport psi) :
    (∫ p in K, psi p • W p) +
      (∫ p in K, fderiv ℝ psi p (EuclideanSpace.single i 1) • u p) = 0 := by
  classical
  have h := m64WeakColumns_compact_lipschitz_test
    ((memLp_indicator_iff_restrict hK).mpr hu) ((memLp_indicator_iff_restrict hK).mpr hW)
    (m64ZeroGreen_indicator_weak_partial hK hu hW hgreen) hp hc
  rwa [m64Integral_smul_indicator hK, m64Integral_smul_indicator hK] at h

theorem m64MatchingGreen_compact_lipschitz
    {m : ℕ} {K : Set LoopPlane} (hK : IsCompact K)
    (u0 u1 W0 W1 : LoopPlane → EuclideanSpace ℝ (Fin m)) {i : Fin 2}
    (hu0 : MemLp u0 2 (volume.restrict K)) (hu1 : MemLp u1 2 (volume.restrict K))
    (hW0 : MemLp W0 2 (volume.restrict K)) (hW1 : MemLp W1 2 (volume.restrict K))
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in K, phi p • W1 p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u1 p) =
      (∫ p in K, phi p • W0 p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u0 p))
    {psi : LoopPlane → ℝ} {L : ℝ≥0} (hp : LipschitzWith L psi) (hc : HasCompactSupport psi) :
    (∫ p in K, psi p • W1 p) +
      (∫ p in K, fderiv ℝ psi p (EuclideanSpace.single i 1) • u1 p) =
    (∫ p in K, psi p • W0 p) +
      (∫ p in K, fderiv ℝ psi p (EuclideanSpace.single i 1) • u0 p) := by
  have hzero (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
      (∫ p in K, phi p • (W1 - W0) p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • (u1 - u0) p) = 0 := by
    have h := hgreen phi hphi
    have hpK : MemLp phi 2 (volume.restrict K) := by
      apply (memLp_two_iff_integrable_sq_norm hphi.continuous.aestronglyMeasurable).mpr
      exact (hphi.continuous.norm.pow 2).continuousOn.integrableOn_compact hK
    have hdK : MemLp (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) 2
        (volume.restrict K) := by
      have hd := (hphi.continuous_fderiv (by simp)).clm_apply
        (continuous_const (y := EuclideanSpace.single i 1))
      apply (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mpr
      exact (hd.norm.pow 2).continuousOn.integrableOn_compact hK
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub (m64L2_test_integrable hW1 hpK) (m64L2_test_integrable hW0 hpK),
      integral_sub (m64L2_test_integrable hu1 hdK) (m64L2_test_integrable hu0 hdK)]
    calc
      _ = ((∫ p in K, phi p • W1 p) +
          ∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u1 p) -
          ((∫ p in K, phi p • W0 p) +
          ∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • u0 p) := by abel
      _ = 0 := sub_eq_zero.mpr h
  have h := m64ZeroGreen_compact_lipschitz hK.measurableSet
    (hu1.sub hu0) (hW1.sub hW0) hzero hp hc
  have hpK : MemLp psi 2 (volume.restrict K) :=
    (hp.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).mono_measure
      Measure.restrict_le_self
  have hdK := (m64CompactLipschitz_fderiv_memLp hp hc i).mono_measure
    (Measure.restrict_le_self (s := K))
  simp only [Pi.sub_apply, smul_sub] at h
  rw [integral_sub (m64L2_test_integrable hW1 hpK) (m64L2_test_integrable hW0 hpK),
    integral_sub (m64L2_test_integrable hu1 hdK) (m64L2_test_integrable hu0 hdK)] at h
  apply sub_eq_zero.mp
  calc
    _ = ((∫ p in K, psi p • W1 p) - ∫ p in K, psi p • W0 p) +
        ((∫ p in K, fderiv ℝ psi p (EuclideanSpace.single i 1) • u1 p) -
          ∫ p in K, fderiv ℝ psi p (EuclideanSpace.single i 1) • u0 p) := by abel
    _ = 0 := h

end PoincareConjecture
