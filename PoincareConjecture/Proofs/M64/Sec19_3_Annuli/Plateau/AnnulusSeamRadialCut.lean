import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamDirectionalTests
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak
import Mathlib.Analysis.SpecialFunctions.SmoothTransition













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak



def m64AnnulusAngularCut : Set LoopPlane := {p | p 0 < 0}



theorem m64AnnulusAngularCut_measurable : MeasurableSet m64AnnulusAngularCut :=
  (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous continuous_const).measurableSet

private def radialCutFactor (j : ℕ) (p : LoopPlane) : ℝ :=
  Real.smoothTransition (-(j : ℝ) * p 0)

private theorem radialCutFactor_smooth (j : ℕ) : ContDiff ℝ ∞ (radialCutFactor j) := by
  have hproj : ContDiff ℝ ∞ (fun p : LoopPlane => p 0) := by
    simpa only [EuclideanSpace.coe_proj] using (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  exact Real.smoothTransition.contDiff.comp (contDiff_const.mul hproj)

private theorem radialCutFactor_radial (j : ℕ) (p : LoopPlane) :
    fderiv ℝ (radialCutFactor j) p (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
  let T : LoopPlane →L[ℝ] ℝ := (-(j : ℝ)) • EuclideanSpace.proj (𝕜 := ℝ) 0
  have hd := ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable
    (by simp) (T p)).hasFDerivAt.comp p
    T.hasFDerivAt
  have h := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (EuclideanSpace.single (1 : Fin 2) 1))
    hd.fderiv
  change fderiv ℝ (fun q : LoopPlane => Real.smoothTransition (-(j : ℝ) * q 0)) p
    (EuclideanSpace.single (1 : Fin 2) 1) = 0
  simpa only [radialCutFactor, Function.comp_def, ContinuousLinearMap.comp_apply,
    T, smul_apply, smul_eq_mul, EuclideanSpace.coe_proj, PiLp.single_apply,
    show (0 : Fin 2) ≠ 1 from by decide, if_false, mul_zero, map_zero] using h

private theorem radialCutFactor_eventually (p : LoopPlane) :
    ∀ᶠ j : ℕ in atTop, radialCutFactor j p = if p 0 < 0 then 1 else 0 := by
  by_cases hp : p 0 < 0
  · have hn : 0 < -p 0 := neg_pos.mpr hp
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (-p 0))
    have hNmul : 1 < (N : ℝ) * (-p 0) := (div_lt_iff₀ hn).mp hN
    filter_upwards [eventually_ge_atTop N] with j hj
    have hNj : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hlarge : 1 ≤ -(j : ℝ) * p 0 := by nlinarith
    simp only [if_pos hp, radialCutFactor, Real.smoothTransition.one_of_one_le hlarge]
  · filter_upwards [] with j
    have hsmall : -(j : ℝ) * p 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) (le_of_not_gt hp)
    simp only [if_neg hp, radialCutFactor, Real.smoothTransition.zero_of_nonpos hsmall]

private theorem radialCutFactor_integral_tendsto {F : LoopPlane → ℝ}
    (hF : Integrable F volume) :
    Tendsto (fun j => ∫ p, radialCutFactor j p * F p) atTop
      (𝓝 (∫ p, m64AnnulusAngularCut.indicator F p)) := by
  apply tendsto_integral_of_dominated_convergence (fun p => ‖F p‖)
  · intro j
    exact ((radialCutFactor_smooth j).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable)
  · exact hF.norm
  · intro j
    filter_upwards [] with p
    rw [norm_mul, radialCutFactor, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)
  · filter_upwards [] with p
    apply tendsto_const_nhds.congr'
    filter_upwards [radialCutFactor_eventually p] with j hj
    by_cases hp : p ∈ m64AnnulusAngularCut
    · have hn : p 0 < 0 := hp
      simp only [hj, if_pos hn, one_mul, indicator_of_mem hp]
    · have hn : ¬p 0 < 0 := hp
      simp only [hj, if_neg hn, zero_mul, indicator_of_notMem hp]



theorem m64WeakPartial_radial_angular_indicator
    {u W : LoopPlane → ℝ} (hu : MemLp u 2 volume) (hW : MemLp W 2 volume)
    (hw : HasWeakPartialDeriv (1 : Fin 2) W u univ) :
    HasWeakPartialDeriv (1 : Fin 2) (m64AnnulusAngularCut.indicator W)
      (m64AnnulusAngularCut.indicator u) univ := by
  intro phi hp hc hs
  let D := fun p => fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1)
  have hpM : MemLp phi 2 volume := hp.continuous.memLp_of_hasCompactSupport hc
  have hdM : MemLp D 2 volume :=
    ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)
  have huD : Integrable (fun p => u p * D p) volume := hu.integrable_mul hdM
  have hWphi : Integrable (fun p => W p * phi p) volume := hW.integrable_mul hpM
  have hleft := radialCutFactor_integral_tendsto huD
  have hright := (radialCutFactor_integral_tendsto hWphi).neg
  have hseq (j : ℕ) : (∫ p, radialCutFactor j p * (u p * D p)) =
      -(∫ p, radialCutFactor j p * (W p * phi p)) := by
    have h := HasWeakPartialDeriv.mul_smooth isOpen_univ hw (radialCutFactor_smooth j)
      (by simpa only [Measure.restrict_univ] using hu.locallyIntegrable (by norm_num))
      (by simpa only [Measure.restrict_univ] using hW.locallyIntegrable (by norm_num))
    have hh := h phi hp hc hs
    simpa only [radialCutFactor_radial, zero_mul, add_zero, Measure.restrict_univ,
      mul_assoc, D] using hh
  have hlim := tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall fun j => (hseq j).symm))
  simp only [Measure.restrict_univ]
  convert hlim using 1
  · apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ m64AnnulusAngularCut <;> simp [hp, D]
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ m64AnnulusAngularCut <;> simp [hp]

open Classical in


theorem m64WeakPartial_radial_angular_piecewise
    {u v W Z : LoopPlane → ℝ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hW : MemLp W 2 volume) (hZ : MemLp Z 2 volume)
    (hw : HasWeakPartialDeriv (1 : Fin 2) W u univ)
    (hz : HasWeakPartialDeriv (1 : Fin 2) Z v univ) :
    HasWeakPartialDeriv (1 : Fin 2) (m64AnnulusAngularCut.piecewise W Z)
      (m64AnnulusAngularCut.piecewise u v) univ := by
  classical
  have hlp {f : LoopPlane → ℝ} (hf : MemLp f 2 volume) :
      MemLp f 2 (volume.restrict univ) := by simpa only [Measure.restrict_univ] using hf
  have hnegv : MemLp (fun p => (-1 : ℝ) * v p) 2 volume := hv.const_mul (-1)
  have hnegZ : MemLp (fun p => (-1 : ℝ) * Z p) 2 volume := hZ.const_mul (-1)
  have hsub : HasWeakPartialDeriv (1 : Fin 2) (fun p => W p - Z p) (fun p => u p - v p) univ := by
    simpa only [neg_one_mul, sub_eq_add_neg] using
      m64WeakPartial_add (hlp hu) (hlp hnegv) (hlp hW) (hlp hnegZ) hw
        (m64WeakPartial_const_mul hz (-1))
  have hind := m64WeakPartial_radial_angular_indicator (hu.sub hv) (hW.sub hZ) hsub
  have hud := (hu.sub hv).indicator m64AnnulusAngularCut_measurable
  have hWd := (hW.sub hZ).indicator m64AnnulusAngularCut_measurable
  have hsum := m64WeakPartial_add (hlp hv) (hlp hud) (hlp hZ) (hlp hWd) hz hind
  have heq (f g : LoopPlane → ℝ) :
      (fun p => g p + m64AnnulusAngularCut.indicator (f - g) p) =
        m64AnnulusAngularCut.piecewise f g := by
    funext p
    by_cases hp : p ∈ m64AnnulusAngularCut
    · simp only [indicator_of_mem hp, Pi.sub_apply, piecewise_eq_of_mem _ _ _ hp]
      ring
    · simp only [indicator_of_notMem hp, add_zero, piecewise_eq_of_notMem _ _ _ hp]
  simpa only [heq] using hsum

end PoincareConjecture
