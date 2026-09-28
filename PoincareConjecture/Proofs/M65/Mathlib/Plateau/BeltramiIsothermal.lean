import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiAnnular
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt











set_option autoImplicit false

noncomputable section

open Set Filter Matrix
open scoped Topology ContDiff ComplexConjugate Matrix.Norms.Elementwise

namespace Complex

private theorem smooth_positiveMetricBeltrami
    (K : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ContDiff ℝ ∞ K) (hpos : ∀ z, (K z).PosDef) :
    ContDiff ℝ ∞ (fun z => positiveMetricBeltrami (K z)) := by
  have he (i j : Fin 2) : ContDiff ℝ ∞ (fun z => K z i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hK
  have hdet : ContDiff ℝ ∞ (fun z => (K z).det) := by
    simpa only [Matrix.det_fin_two] using
      ((he 0 0).mul (he 1 1)).sub ((he 0 1).mul (he 1 0))
  have hsqrt := hdet.sqrt (fun z => (hpos z).det_pos.ne')
  have hden := ((he 0 0).add (he 1 1)).add
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => (2 : ℝ))).mul hsqrt)
  have hdenpos (z : ℂ) : 0 < K z 0 0 + K z 1 1 + 2 * Real.sqrt (K z).det := by
    linarith [(hpos z).diag_pos (i := 0), (hpos z).diag_pos (i := 1),
      Real.sqrt_nonneg (K z).det]
  have hnum := (ofRealCLM.contDiff.comp ((he 0 0).sub (he 1 1))).add
    ((ofRealCLM.contDiff.comp
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => (2 : ℝ))).mul (he 0 1))).mul
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => I)))
  simpa only [positiveMetricBeltrami, div_eq_mul_inv] using!
    hnum.mul ((ofRealCLM.contDiff.comp hden).inv
      (fun z => ofReal_ne_zero.mpr (hdenpos z).ne'))




theorem positiveMetricBeltrami_inverse_quadratic
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.PosDef)
    (L A : ℂ →L[ℝ] ℂ) (hLA : L.comp A = ContinuousLinearMap.id ℝ ℂ)
    (heq : L 1 + I * L I = positiveMetricBeltrami K * (L 1 - I * L I)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
      K 0 0 * (A v).re ^ 2 + 2 * K 0 1 * (A v).re * (A v).im +
        K 1 1 * (A v).im ^ 2 = c * ‖v‖ ^ 2 := by
  let w : ℂ := (L 1 - I * L I) / 2
  have hv (v : ℂ) : w * (A v + positiveMetricBeltrami K * conj (A v)) = v := by
    rw [← linearMap_beltrami_formula L (positiveMetricBeltrami K) heq (A v)]
    exact DFunLike.congr_fun hLA v
  have hw : w ≠ 0 := by
    intro hzero
    have hh := hv 1
    rw [hzero, zero_mul] at hh
    exact zero_ne_one hh
  have hn : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  let d : ℝ := (K 0 0 + K 1 1 + 2 * Real.sqrt K.det) / 4
  have hd : 0 < d := by
    have h0 := hK.diag_pos (i := 0)
    have h1 := hK.diag_pos (i := 1)
    dsimp only [d]
    positivity
  refine ⟨d / ‖w‖ ^ 2, div_pos hd hn, ?_⟩
  intro v
  rw [positiveMetricBeltrami_quadratic K hK (A v)]
  have hnorm : ‖v‖ ^ 2 =
      ‖w‖ ^ 2 * ‖A v + positiveMetricBeltrami K * conj (A v)‖ ^ 2 := by
    calc
      _ = ‖w * (A v + positiveMetricBeltrami K * conj (A v))‖ ^ 2 :=
        congrArg (fun x : ℂ => ‖x‖ ^ 2) (hv v).symm
      _ = _ := by rw [norm_mul, mul_pow]
  change d * _ = d / ‖w‖ ^ 2 * _
  rw [hnorm]
  field_simp [hn.ne']





theorem exists_smooth_disk_isothermal_coordinates
    (K : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ContDiff ℝ ∞ K) (hpos : ∀ z, (K z).PosDef) (δ : ℝ)
    (hzero : ∀ᶠ z in 𝓝 (0 : ℂ), K z = δ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hout : ∀ z, 1 ≤ ‖z‖ → K z = δ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ∃ φ : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (φ : ℂ → ℂ) ∧ ContDiff ℝ ∞ (φ.symm : ℂ → ℂ) ∧
      φ 0 = 0 ∧ φ 1 = 1 ∧ (∀ z, ‖φ z‖ ≤ 1 ↔ ‖z‖ ≤ 1) ∧
      (∀ z, ‖φ z‖ < 1 ↔ ‖z‖ < 1) ∧
      ∀ z, ‖z‖ ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∀ v : ℂ,
        K (φ z) 0 0 * (fderiv ℝ (φ : ℂ → ℂ) z v).re ^ 2 +
          2 * K (φ z) 0 1 * (fderiv ℝ (φ : ℂ → ℂ) z v).re *
            (fderiv ℝ (φ : ℂ → ℂ) z v).im +
          K (φ z) 1 1 * (fderiv ℝ (φ : ℂ → ℂ) z v).im ^ 2 = c * ‖v‖ ^ 2 := by
  let μ : ℂ → ℂ := fun z => positiveMetricBeltrami (K z)
  have hiso : positiveMetricBeltrami (δ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
    simp [positiveMetricBeltrami]
  have hμzero : ∀ᶠ z in 𝓝 (0 : ℂ), μ z = 0 := by
    filter_upwards [hzero] with z hz
    exact (congrArg positiveMetricBeltrami hz).trans hiso
  have hμout (z : ℂ) (hz : 1 ≤ ‖z‖) : μ z = 0 :=
    (congrArg positiveMetricBeltrami (hout z hz)).trans hiso
  obtain ⟨f, hf, hfi, hf0, hf1, hclosed, hopen, heq⟩ :=
    exists_annular_disk_beltrami_diffeomorphism μ (smooth_positiveMetricBeltrami K hK hpos)
      hμzero hμout (fun z => norm_positiveMetricBeltrami_lt_one (K z) (hpos z))
  refine ⟨f.symm, hfi, hf, ?_, ?_, ?_, ?_, ?_⟩
  · exact f.symm_apply_eq.mpr hf0.symm
  · exact f.symm_apply_eq.mpr hf1.symm
  · intro z
    simpa only [f.apply_symm_apply] using (hclosed (f.symm z)).symm
  · intro z
    simpa only [f.apply_symm_apply] using (hopen (f.symm z)).symm
  · intro z hz
    have hin : ‖f.symm z‖ ≤ 1 := (hclosed (f.symm z)).mp (by simpa using hz)
    have hLA : (fderiv ℝ (f : ℂ → ℂ) (f.symm z)).comp
        (fderiv ℝ (f.symm : ℂ → ℂ) z) = ContinuousLinearMap.id ℝ ℂ := by
      have hh := fderiv_comp z (hf.differentiable (by simp)).differentiableAt
        (hfi.differentiable (by simp)).differentiableAt
      simpa only [Function.comp_def, f.apply_symm_apply, fderiv_fun_id] using hh.symm
    exact positiveMetricBeltrami_inverse_quadratic (K (f.symm z)) (hpos _) _ _ hLA
      (heq _ hin)

end Complex
