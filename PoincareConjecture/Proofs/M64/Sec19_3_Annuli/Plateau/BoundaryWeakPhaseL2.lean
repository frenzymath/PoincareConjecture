import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryVerticalPrimitive
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.NonnegativeApproximation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness
open Poincare.Analysis.Sobolev.DifferenceQuotient

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)





theorem m64WeakPhase_smooth_pairing_sq_le
    (u V : LoopPlane → ℝ) (b : ℝ → ℝ)
    (hV : MemLp V 2 mu) (hb : MemLp b 2 nu)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x))
    (f : LoopPlane → ℝ) (hf : ContDiff ℝ ∞ f) :
    (∫ p in S, f p * u p) ^ 2 ≤
      2 * (∫ p in S, (f p) ^ 2) *
        ((∫ p in S, (V p) ^ 2) + ∫ x in Icc (0 : ℝ) curvePeriod, (b x) ^ 2) := by
  let phi := m64VerticalPrimitive f
  have hphi : ContDiff ℝ ∞ phi := m64VerticalPrimitive_contDiff hf
  have hp : MemLp phi 2 mu := by
    apply (memLp_two_iff_integrable_sq hphi.continuous.aestronglyMeasurable).mpr
    exact (hphi.continuous.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hbottom : Continuous (fun x => phi (annulusPoint x 0)) :=
    hphi.continuous.comp (by unfold annulusPoint; fun_prop)
  have ht : MemLp (fun x => phi (annulusPoint x 0)) 2 nu :=
    (memLp_two_iff_integrable_sq hbottom.aestronglyMeasurable).mpr
      (hbottom.pow 2).integrableOn_Icc
  have hg := hgreen phi (hphi.of_le (by simp)) (m64VerticalPrimitive_top f)
  simp only [phi, m64VerticalPrimitive_vertical_derivative hf, neg_mul,
    integral_neg] at hg
  have hbounds := m64VerticalPrimitive_l2_bounds hf
  have hv := (M64Uniformization.scalar_integral_mul_sq_le hp hV).trans
    (mul_le_mul_of_nonneg_right hbounds.1 (integral_nonneg (fun _ => sq_nonneg _)))
  have hb' := (M64Uniformization.scalar_integral_mul_sq_le ht hb).trans
    (mul_le_mul_of_nonneg_right hbounds.2 (integral_nonneg (fun _ => sq_nonneg _)))
  dsimp only [phi] at hv hb'
  have heq : (∫ p in S, f p * u p) = (∫ p in S, m64VerticalPrimitive f p * V p) +
      ∫ x in Icc (0 : ℝ) curvePeriod, m64VerticalPrimitive f (annulusPoint x 0) * b x := by
    linarith
  rw [heq]
  nlinarith [sq_nonneg ((∫ p in S, m64VerticalPrimitive f p * V p) -
    ∫ x in Icc (0 : ℝ) curvePeriod, m64VerticalPrimitive f (annulusPoint x 0) * b x)]






theorem m64WeakPhase_lower_trace_l2_bound
    (u V : LoopPlane → ℝ) (b : ℝ → ℝ)
    (hu : MemLp u 2 mu) (hV : MemLp V 2 mu) (hb : MemLp b 2 nu)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x)) :
    (∫ p in S, (u p) ^ 2) ≤
      2 * ((∫ p in S, (V p) ^ 2) + ∫ x in Icc (0 : ℝ) curvePeriod, (b x) ^ 2) := by
  let U := (S).indicator u
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict measurableSet_interior).mpr hu
  let r := fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)
  have hr (j : ℕ) : 0 < r j := pow_pos (by norm_num) _
  have hrz : Tendsto r atTop (𝓝 0) := by
    simpa only [r, pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
  let f (j : ℕ) := mollifyEps (hr j) U
  have hf (j : ℕ) : ContDiff ℝ ∞ (f j) :=
    mollifyEps_contDiff (hr j) (hU.locallyIntegrable (by norm_num))
  have hF (j : ℕ) : MemLp (f j) 2 mu := by
    apply (memLp_two_iff_integrable_sq (hf j).continuous.aestronglyMeasurable).mpr
    exact ((hf j).continuous.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hlim : Tendsto (fun j => eLpNorm (f j - u) 2 mu) atTop (𝓝 0) := by
    have hglobal := tendsto_eLpNorm_mollifyEps_sub hr hrz (by norm_num) (by norm_num) hU
    have hbound (j : ℕ) : eLpNorm (f j - u) 2 mu ≤ eLpNorm (f j - U) 2 volume := by
      calc
        _ = eLpNorm (f j - U) 2 mu := eLpNorm_congr_ae (by
          filter_upwards [ae_restrict_mem measurableSet_interior] with p hp
          simp only [Pi.sub_apply, U, indicator_of_mem hp])
        _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
      (fun _ => bot_le) hbound
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hF u hu).mpr hlim
  have hsqnorm (g : LoopPlane → ℝ) (hg : MemLp g 2 mu) :
      ‖hg.toLp g‖ ^ 2 = ∫ p in S, (g p) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with p hp
    simp only [real_inner_self_eq_norm_sq, hp, Real.norm_eq_abs, sq_abs]
  have hnorm : Tendsto (fun j => ∫ p in S, (f j p) ^ 2) atTop
      (𝓝 (∫ p in S, (u p) ^ 2)) := by
    simpa only [hsqnorm] using hLp.norm.pow 2
  let A := testIntegral (F := ℝ) u hu
  have hpair : Tendsto (fun j => ∫ p in S, f j p * u p) atTop
      (𝓝 (∫ p in S, (u p) ^ 2)) := by
    have hh := (A.continuous.tendsto (hu.toLp u)).comp hLp
    simpa only [A, Function.comp_def, testIntegral_toLp, smul_eq_mul, mul_comm, ← sq] using hh
  have hsq : (∫ p in S, (u p) ^ 2) ^ 2 ≤
      2 * (∫ p in S, (u p) ^ 2) *
        ((∫ p in S, (V p) ^ 2) + ∫ x in Icc (0 : ℝ) curvePeriod, (b x) ^ 2) :=
    le_of_tendsto_of_tendsto' (hpair.pow 2) ((hnorm.const_mul 2).mul_const _)
      (fun j => m64WeakPhase_smooth_pairing_sq_le u V b hV hb hgreen (f j) (hf j))
  have hnonneg : 0 ≤ ∫ p in S, (u p) ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hnonneg' : 0 ≤ (∫ p in S, (V p) ^ 2) +
      ∫ x in Icc (0 : ℝ) curvePeriod, (b x) ^ 2 :=
    add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _))
  nlinarith

end PoincareConjecture
