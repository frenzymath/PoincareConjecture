import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralSmoothing
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential








set_option autoImplicit false

noncomputable section

namespace Poincare.Analysis.Dirichlet.Spectral

open Set
open scoped Topology InnerProductSpace NNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

private def heatSeries (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (t : ℝ) :
    FormalMultilinearSeries ℝ ℝ (H →L[ℝ] H) :=
  fun k => ContinuousMultilinearMap.mkPiRing ℝ (Fin k)
    (((-1 : ℝ) ^ k / (k.factorial : ℝ)) • heatPower b lam k t)

private theorem heatSeries_radius (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t ≤ (heatSeries b lam t).radius := by
  let r : NNReal := ⟨t, ht.le⟩
  have hr : (r : ENNReal) ≤ (heatSeries b lam t).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ 1
    intro k
    have hf : (0 : ℝ) < k.factorial := by positivity
    have hp : 0 < t ^ k := pow_pos ht k
    simp only [heatSeries, ContinuousMultilinearMap.norm_mkPiRing, norm_smul,
      norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg hf.le,
      NNReal.coe_mk]
    calc
      (1 / (k.factorial : ℝ) * ‖heatPower b lam k t‖) * t ^ k ≤
          (1 / (k.factorial : ℝ) * ((k.factorial : ℝ) / t ^ k)) * t ^ k := by
        gcongr
        exact norm_heatPower_le b lam k ht
      _ = 1 := by field_simp
  calc
    ENNReal.ofReal t = (r : ENNReal) := by
      rw [ENNReal.coe_nnreal_eq]
      rfl
    _ ≤ (heatSeries b lam t).radius := hr

private theorem heatSeries_sum (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0)
    {t h : ℝ} (ht : 0 < t) (hh : ‖h‖ < t) :
    (heatSeries b lam t).sum h = heatPower b lam 0 (t + h) := by
  have hth : 0 < t + h := by
    have hh' : -t < h := by
      have hh'' : |h| < t := by simpa [Real.norm_eq_abs] using hh
      exact (abs_lt.mp hh'').1
    linarith
  have hmem : h ∈ Metric.eball 0 (heatSeries b lam t).radius := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    calc
      ENNReal.ofReal ‖h‖ < ENNReal.ofReal t :=
        (ENNReal.ofReal_lt_ofReal_iff ht).mpr hh
      _ = ENNReal.ofNNReal (⟨t, ht.le⟩ : NNReal) := by
        symm
        exact ENNReal.coe_nnreal_eq _
      _ ≤ (heatSeries b lam t).radius := by
        have hr := heatSeries_radius b lam ht
        exact (ENNReal.coe_nnreal_eq (⟨t, ht.le⟩ : NNReal)).symm ▸ hr
  have hs := (heatSeries b lam t).hasSum hmem
  ext u
  apply b.repr.injective
  ext i
  let L : (H →L[ℝ] H) →L[ℝ] ℝ :=
    (innerSL ℝ (b i)).comp ((ContinuousLinearMap.apply ℝ H) u)
  have hcoord := L.hasSum hs
  have hexp := (NormedSpace.expSeries_div_hasSum_exp (-(lam i : ℝ) * h)).mul_right
    (Real.exp (-(lam i : ℝ) * t) * b.repr u i)
  rw [← Real.exp_eq_exp_ℝ] at hexp
  have hterms : (fun k => L ((heatSeries b lam t k) (fun _ => h))) =
      (fun k => (-(lam i : ℝ) * h) ^ k / (k.factorial : ℝ) *
        (Real.exp (-(lam i : ℝ) * t) * b.repr u i)) := by
    funext k
    simp only [heatSeries, ContinuousMultilinearMap.mkPiRing_apply,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_smul,
      smul_eq_mul]
    change h ^ k * ((-1 : ℝ) ^ k / (k.factorial : ℝ) *
      inner ℝ (b i) (heatPower b lam k t u)) = _
    rw [← b.repr_apply_apply, heatPower_repr b lam k ht]
    rw [show -(lam i : ℝ) * h = (-1 : ℝ) * (lam i : ℝ) * h by ring,
      mul_pow, mul_pow]
    ring
  rw [hterms] at hcoord
  have heq := hcoord.unique hexp
  change inner ℝ (b i) ((heatSeries b lam t).sum h u) = _ at heq
  rw [← b.repr_apply_apply] at heq
  rw [heq, heatPower_repr b lam 0 hth, pow_zero, one_mul]
  rw [show -(lam i : ℝ) * (t + h) = -(lam i : ℝ) * h + -(lam i : ℝ) * t by ring,
    Real.exp_add]
  ring


theorem analyticOnNhd_heatPower_zero (b : HilbertBasis ι ℝ H)
    (lam : ι → ℝ≥0) :
    AnalyticOnNhd ℝ (fun t : ℝ => heatPower b lam 0 t) (Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  have hp : HasFPowerSeriesOnBall (fun s => heatPower b lam 0 s)
      (heatSeries b lam t) t (ENNReal.ofReal t) := by
    refine ⟨by simpa using heatSeries_radius b lam ht', ENNReal.ofReal_pos.mpr ht', ?_⟩
    intro h hh
    have hh' : ‖h‖ < t := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right] at hh
      exact (ENNReal.ofReal_lt_ofReal_iff ht').mp (by simpa using hh)
    rw [← heatSeries_sum b lam ht hh']
    exact (heatSeries b lam t).hasSum
      (show h ∈ Metric.eball 0 (heatSeries b lam t).radius from by
        rw [Metric.mem_eball, edist_dist, dist_zero_right]
        exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff ht').mpr hh')
          (heatSeries_radius b lam ht'))
  exact hp.analyticAt

theorem heat_injective (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (t : ℝ≥0) :
    Function.Injective (heat b lam t) := by
  intro u v huv
  apply b.repr.injective
  ext i
  have hi := congrArg (fun z => b.repr z i) huv
  rw [heat_repr, heat_repr] at hi
  exact (mul_left_cancel₀ (ne_of_gt (coefficient_pos lam t i)) hi)

end Poincare.Analysis.Dirichlet.Spectral
