import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNaturalGrowthTest
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNormalZeroExtension

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

theorem m64NaturalGrowth_face_zero_extension_test
    {O : Set LoopPlane} (hO : IsOpen O)
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O)
    (hzero : ∀ p : LoopPlane, p 1 = 0 → phi p = 0)
    (hFzero : ∀ i p, p 1 ≤ 0 → F i p = 0)
    (hbzero : ∀ p, p 1 ≤ 0 → b p = 0)
    (heq : ∀ psi : LoopPlane → ℝ, ContDiff ℝ ∞ psi →
      HasCompactSupport psi →
      tsupport psi ⊆ O ∩ {p : LoopPlane | 0 < p 1} →
      (∫ p, ∑ i : Fin 2, F i p *
        fderiv ℝ psi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * psi p) :
    (∫ p, ∑ i : Fin 2, F i p *
      fderiv ℝ phi p (EuclideanSpace.single i 1)) =
      ∫ p, b p * phi p := by
  let H : Set LoopPlane := {p : LoopPlane | 0 < p 1}
  have hH : IsOpen H := isOpen_lt continuous_const
    (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
  have hphiLp : MemLp phi 2 volume :=
    hp.continuous.memLp_of_hasCompactSupport hc
  have hderivLp (i : Fin 2) : MemLp
      (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) 2 volume :=
    ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
  have hweak (i : Fin 2) : HasWeakPartialDeriv i
      (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) phi H :=
    HasWeakPartialDeriv.of_contDiff hH (hp.of_le (by norm_num))
  have hsupport : support (H.indicator phi) ⊆ support phi := by
    intro p hp_support
    by_cases hpH : p ∈ H
    · simpa only [mem_support, indicator_of_mem hpH] using hp_support
    · simp only [mem_support, indicator_of_notMem hpH, ne_eq,
        not_true_eq_false] at hp_support
  have htsupport : tsupport (H.indicator phi) ⊆ tsupport phi :=
    closure_mono hsupport
  have hcompact : HasCompactSupport (H.indicator phi) := hc.mono hsupport
  have hU : Continuous (H.indicator phi) := by
    simpa only [H] using m64Continuous_normalZeroExtension_continuous
      hp.continuous hzero
  have hzeroU : ∀ p : LoopPlane, p 1 < 0 → H.indicator phi p = 0 := by
    intro p hpneg
    rw [indicator_of_notMem]
    exact not_lt.mpr hpneg.le
  have hUlp : MemLp (H.indicator phi) 2 volume := by
    exact (memLp_indicator_iff_restrict hH.measurableSet).mpr (hphiLp.restrict H)
  have hUlpi (i : Fin 2) : MemLp
      (H.indicator (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1))) 2 volume := by
    exact (memLp_indicator_iff_restrict hH.measurableSet).mpr ((hderivLp i).restrict H)
  have hUweak (i : Fin 2) : HasWeakPartialDeriv i
      (H.indicator (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)))
      (H.indicator phi) univ := by
    exact m64Continuous_normalZeroExtension_weak i hp.continuous hzero
      (hphiLp.restrict H) ((hderivLp i).restrict H) (hweak i)
  have htest :
      (∫ p, ∑ i : Fin 2, F i p *
        H.indicator (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p) =
        ∫ p, b p * H.indicator phi p := by
    apply m64NaturalGrowth_zero_boundary_test hO hF hb hU hcompact
      (htsupport.trans hs) hUlp hUlpi hUweak hzeroU
    intro psi hpsi hpsic hpsis
    exact heq psi hpsi hpsic (by simpa only [H] using hpsis)
  have hleft :
      (fun p => ∑ i : Fin 2, F i p *
        H.indicator (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p) =
      fun p => ∑ i : Fin 2, F i p *
        fderiv ℝ phi p (EuclideanSpace.single i 1) := by
    funext p
    by_cases hpH : p ∈ H
    · simp only [indicator_of_mem hpH]
    · have hp0 : p 1 ≤ 0 := le_of_not_gt hpH
      simp only [indicator_of_notMem hpH]
      simp only [hFzero _ p hp0, zero_mul, Finset.sum_const_zero]
  have hright :
      (fun p => b p * H.indicator phi p) = fun p => b p * phi p := by
    funext p
    by_cases hpH : p ∈ H
    · simp only [indicator_of_mem hpH]
    · have hp0 : p 1 ≤ 0 := le_of_not_gt hpH
      simp only [indicator_of_notMem hpH]
      rw [hbzero p hp0, zero_mul, zero_mul]
  simpa only [hleft, hright] using htest

end PoincareConjecture
