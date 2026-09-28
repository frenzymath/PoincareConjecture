import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRealTraceCompactness

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64MonotoneAffinePhase_boundary_mean_bounds
    (b : ℝ → ℝ) (hb : Monotone b) {D : ℝ}
    (hp : ∀ x, b (x + curvePeriod) = b x + D) :
    curvePeriod * b 0 ≤ ∫ x in Icc (0 : ℝ) curvePeriod, b x ∧
      (∫ x in Icc (0 : ℝ) curvePeriod, b x) ≤ curvePeriod * (b 0 + D) := by
  have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hi : IntegrableOn b (Icc (0 : ℝ) curvePeriod) :=
    (hb.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hlo := setIntegral_mono_on
    (integrableOn_const (μ := volume) (C := b 0) isCompact_Icc.measure_ne_top)
    hi measurableSet_Icc (fun x hx => hb hx.1)
  have hhi := setIntegral_mono_on hi
    (integrableOn_const (μ := volume) (C := b 0 + D) isCompact_Icc.measure_ne_top)
    measurableSet_Icc (fun x hx => by
      have h := hb hx.2
      have hzero := hp 0
      simp only [zero_add] at hzero
      rwa [hzero] at h)
  simp only [setIntegral_const, Real.volume_real_Icc, sub_zero, max_eq_left hP,
    smul_eq_mul] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem m64WeakPhase_upper_zero_bound
    (u v : LoopPlane → ℝ) (b0 b1 : ℝ → ℝ)
    (hv : MemLp v 2 mu) (hm0 : Monotone b0) (hm1 : Monotone b1)
    {D B C : ℝ} (hp0 : ∀ x, b0 (x + curvePeriod) = b0 x + D)
    (hp1 : ∀ x, b1 (x + curvePeriod) = b1 x + D)
    (hB : |b0 0| ≤ B) (hC : (∫ p in S, v p ^ 2) ≤ C)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * v p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) * b1 x - phi (annulusPoint x 0) * b0 x) :
    |b1 0| ≤ B + |D| + (volume.real S + C) / (2 * curvePeriod) := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have hi0 : Integrable b0 nu := (hm0.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hi1 : Integrable b1 nu := (hm1.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have hflux := hgreen (fun _ => 1) contDiff_const
  simp only [one_mul, fderiv_const_apply, zero_apply, zero_mul, integral_zero,
    add_zero, integral_sub hi1 hi0] at hflux
  have hvi : Integrable v mu := hv.integrable (by norm_num)
  have hconst : Integrable (fun _ : LoopPlane => (1 : ℝ)) mu := integrable_const 1
  have hupper := integral_mono (hvi.const_mul 2) (hconst.add hv.integrable_sq)
    (fun p => by dsimp only [Pi.add_apply]; nlinarith [sq_nonneg (v p - 1)])
  have hlower := integral_mono (hvi.const_mul (-2)) (hconst.add hv.integrable_sq)
    (fun p => by dsimp only [Pi.add_apply]; nlinarith [sq_nonneg (v p + 1)])
  simp only [Pi.add_apply] at hupper hlower
  rw [integral_add hconst hv.integrable_sq] at hupper hlower
  simp only [integral_const_mul, integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] at hupper hlower
  have hm0b := m64MonotoneAffinePhase_boundary_mean_bounds b0 hm0 hp0
  have hm1b := m64MonotoneAffinePhase_boundary_mean_bounds b1 hm1 hp1
  have hb0 := abs_le.mp hB
  have hd0 : D ≤ |D| := le_abs_self D
  have hd1 : -D ≤ |D| := neg_le_abs D
  have hdiv : (volume.real S + C) / (2 * curvePeriod) * curvePeriod =
      (volume.real S + C) / 2 := by field_simp
  apply (abs_le).mpr
  constructor <;> apply (mul_le_mul_iff_right₀ hP).mp
  · nlinarith [hm0b.1, hm1b.2]
  · nlinarith [hm0b.2, hm1b.1]

end PoincareConjecture
