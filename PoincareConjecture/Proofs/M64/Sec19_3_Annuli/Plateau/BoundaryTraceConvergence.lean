import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTraceInterpolation
import Mathlib.MeasureTheory.Function.L2Space












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

private theorem scalar_toLp_norm_sq {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} (hf : MemLp f 2 mu) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem cauchySeq_of_trace_interpolation
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {u : ℕ → X} {v : ℕ → Y} {C : ℝ} (hC : 0 ≤ C)
    (hu : CauchySeq u)
    (h : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ j k,
      dist (v j) (v k) ^ 2 ≤ (2 / delta) * dist (u j) (u k) ^ 2 + 8 * delta * C) :
    CauchySeq v := by
  apply Metric.cauchySeq_iff.mpr
  intro epsilon hepsilon
  let delta := min 1 (epsilon ^ 2 / (32 * (C + 1)))
  have hd : 0 < delta := lt_min zero_lt_one (div_pos (sq_pos_of_pos hepsilon) (by positivity))
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdsmall : delta * (32 * (C + 1)) ≤ epsilon ^ 2 :=
    (le_div_iff₀ (by positivity : 0 < 32 * (C + 1))).mp (min_le_right _ _)
  let eta := Real.sqrt (epsilon ^ 2 * delta / 8)
  have heta : 0 < eta := Real.sqrt_pos.mpr (by positivity)
  have heta2 : eta ^ 2 = epsilon ^ 2 * delta / 8 := Real.sq_sqrt (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu eta heta
  refine ⟨N, fun j hj k hk => ?_⟩
  have hdist2 : dist (u j) (u k) ^ 2 < eta ^ 2 :=
    (sq_lt_sq₀ dist_nonneg heta.le).mpr (hN j hj k hk)
  have hbulk : (2 / delta) * dist (u j) (u k) ^ 2 ≤ epsilon ^ 2 / 4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hboundary := h delta hd hd1 j k
  have hcollar : 8 * delta * C ≤ epsilon ^ 2 / 4 := by nlinarith
  apply (sq_lt_sq₀ dist_nonneg hepsilon.le).mp
  nlinarith [sq_pos_of_pos hepsilon]



theorem m64Annulus_lower_trace_cauchySeq
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in interior m64AnnulusDomain,
      (fderiv ℝ (f j) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2) ≤ C)
    (hU : ∀ j, MemLp (f j) 2 (volume.restrict (interior m64AnnulusDomain)))
    (hbulk : CauchySeq (fun j => (hU j).toLp (f j))) :
    ∃ hT : ∀ j, MemLp (fun x => f j (annulusPoint x 0)) 2
        (volume.restrict (Icc (0 : ℝ) curvePeriod)),
      CauchySeq (fun j => (hT j).toLp (fun x => f j (annulusPoint x 0))) := by
  have hc (j : ℕ) : Continuous (fun x => f j (annulusPoint x 0)) := by
    apply (hf j).continuous.comp
    unfold annulusPoint
    fun_prop
  have hT (j : ℕ) : MemLp (fun x => f j (annulusPoint x 0)) 2
      (volume.restrict (Icc (0 : ℝ) curvePeriod)) := by
    apply (memLp_two_iff_integrable_sq (hc j).aestronglyMeasurable).mpr
    have hc2 : Continuous (fun x => f j (annulusPoint x 0) ^ 2) := (hc j).pow 2
    exact hc2.integrableOn_Icc
  have hD (j : ℕ) : IntegrableOn
      (fun p => (fderiv ℝ (f j) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2)
      (interior m64AnnulusDomain) volume :=
    ((((hf j).continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).continuousOn
      |>.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hC0 : 0 ≤ C := (integral_nonneg fun _ => sq_nonneg _).trans (hC 0)
  refine ⟨hT, cauchySeq_of_trace_interpolation hC0 hbulk ?_⟩
  intro delta hd hd1 j k
  have henergy : (∫ p in interior m64AnnulusDomain,
      (fderiv ℝ (fun p => f j p - f k p) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2)
      ≤ 4 * C := by
    have hfd (p : LoopPlane) :
        fderiv ℝ (fun p => f j p - f k p) p (EuclideanSpace.single (1 : Fin 2) 1) =
        fderiv ℝ (f j) p (EuclideanSpace.single (1 : Fin 2) 1) -
          fderiv ℝ (f k) p (EuclideanSpace.single (1 : Fin 2) 1) := by
      rw [fderiv_fun_sub ((hf j).differentiable (by simp) p)
        ((hf k).differentiable (by simp) p), sub_apply]
    have hdiff : IntegrableOn (fun p =>
        (fderiv ℝ (fun p => f j p - f k p) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2)
        (interior m64AnnulusDomain) volume :=
      (((((hf j).sub (hf k)).continuous_fderiv (by simp)).clm_apply
        continuous_const).pow 2).continuousOn
        |>.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
    calc
      _ ≤ ∫ p in interior m64AnnulusDomain,
          (2 * (fderiv ℝ (f j) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2 +
            2 * (fderiv ℝ (f k) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2) := by
        apply integral_mono hdiff (((hD j).const_mul 2).add ((hD k).const_mul 2))
        intro p
        simp only [Pi.add_apply, hfd]
        nlinarith [sq_nonneg (fderiv ℝ (f j) p (EuclideanSpace.single (1 : Fin 2) 1) +
          fderiv ℝ (f k) p (EuclideanSpace.single (1 : Fin 2) 1))]
      _ = 2 * (∫ p in interior m64AnnulusDomain,
          (fderiv ℝ (f j) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2) +
          2 * (∫ p in interior m64AnnulusDomain,
          (fderiv ℝ (f k) p (EuclideanSpace.single (1 : Fin 2) 1)) ^ 2) := by
        rw [integral_add ((hD j).const_mul 2) ((hD k).const_mul 2),
          integral_const_mul, integral_const_mul]
      _ ≤ 4 * C := by linarith [hC j, hC k]
  have htrace := m64Annulus_lower_trace_interpolation ((hf j).sub (hf k)) hd hd1
  have hscale := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 2 * delta)
  simp only [dist_eq_norm, ← MemLp.toLp_sub, scalar_toLp_norm_sq]
  change (∫ x in Icc (0 : ℝ) curvePeriod,
      (f j (annulusPoint x 0) - f k (annulusPoint x 0)) ^ 2) ≤
    (2 / delta) * (∫ p in interior m64AnnulusDomain, (f j p - f k p) ^ 2) +
      8 * delta * C
  linarith

end PoincareConjecture
