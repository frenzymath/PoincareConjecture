import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerMetric
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 5

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Euler

private theorem ae_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure LoopPlane}
    {A : LoopPlane → E →L[ℝ] F} {v : LoopPlane → E}
    (hA : AEStronglyMeasurable A μ) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun z => A z (v z)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hv)

private theorem quadratic_hasDerivAt {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (x w a b : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) *
      g.inner (x + s • w) (a + s • b) (a + s • b))
      ((1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients (x + t • w) w
        (a + t • b) (a + t • b) + g.inner (x + t • w) b (a + t • b)) t := by
  have hx : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa +instances only [Pi.add_apply, id_eq, zero_add, one_smul] using!
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const w)
  have ha : HasDerivAt (fun s : ℝ => a + s • b) b t := by
    simpa +instances only [Pi.add_apply, id_eq, zero_add, one_smul] using!
      (hasDerivAt_const t a).add ((hasDerivAt_id t).smul_const b)
  have hG := ((g.contDiffAt_euclideanCoefficients (x + t • w)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t hx
  convert! (((hG.clm_apply ha).clm_apply ha).const_mul (1 / 2 : ℝ)) using 1
  simp only [add_apply]
  change (1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients (x + t • w) w
      (a + t • b) (a + t • b) + g.inner (x + t • w) b (a + t • b) =
    (1 / 2 : ℝ) * (fderiv ℝ g.euclideanCoefficients (x + t • w) w
      (a + t • b) (a + t • b) + g.inner (x + t • w) b (a + t • b) +
      g.inner (x + t • w) (a + t • b) b)
  rw [g.symm (x + t • w) (a + t • b) b]
  ring

private theorem quadratic_derivative_bound {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (y w a b : EuclideanSpace ℝ (Fin N)) {C D L t : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hG : ‖g.euclideanCoefficients y‖ ≤ C)
    (hDG : ‖fderiv ℝ g.euclideanCoefficients y‖ ≤ D)
    (hw : ‖w‖ ≤ L) (ht : |t| ≤ 1) :
    ‖(1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients y w (a + t • b) (a + t • b) +
      g.inner y b (a + t • b)‖ ≤ (D * L + 2 * C) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hp : ‖a + t • b‖ ≤ ‖a‖ + ‖b‖ := by
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hDapp : ‖fderiv ℝ g.euclideanCoefficients y w‖ ≤ D * L :=
    ((fderiv ℝ g.euclideanCoefficients y).le_opNorm w).trans
      (mul_le_mul hDG hw (norm_nonneg _) hD)
  have hfirst : ‖fderiv ℝ g.euclideanCoefficients y w (a + t • b) (a + t • b)‖ ≤
      D * L * (‖a‖ + ‖b‖) ^ 2 := by
    refine ((fderiv ℝ g.euclideanCoefficients y w).le_opNorm₂ _ _).trans ?_
    calc
      _ ≤ (D * L) * (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) := by gcongr
      _ = _ := by ring
  have hsecond : ‖g.inner y b (a + t • b)‖ ≤ C * ‖b‖ * (‖a‖ + ‖b‖) := by
    exact (g.euclideanCoefficients y |>.le_opNorm₂ b (a + t • b)).trans (by gcongr)
  have hn := (norm_add_le ((1 / 2 : ℝ) *
    fderiv ℝ g.euclideanCoefficients y w (a + t • b) (a + t • b))
    (g.inner y b (a + t • b))).trans (add_le_add
      (by simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        using mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 1 / 2)) hsecond)
  have hs : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hb : ‖b‖ * (‖a‖ + ‖b‖) ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg ‖a‖, sq_nonneg ‖b‖]
  nlinarith only [hn, mul_le_mul_of_nonneg_left hs (mul_nonneg hD hL),
    mul_le_mul_of_nonneg_left hb hC]

set_option maxHeartbeats 1800000 in

theorem hasDerivAt_integral_quadratic {N : ℕ} {μ : Measure LoopPlane}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (X W A Z : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hX : AEStronglyMeasurable X μ) (hW : AEStronglyMeasurable W μ)
    (hA : MemLp A 2 μ) (hZ : MemLp Z 2 μ)
    {L r : ℝ} (hL : 0 ≤ L) (hr : 0 < r) (hWb : ∀ᵐ z ∂μ, ‖W z‖ ≤ L)
    (K : Set (EuclideanSpace ℝ (Fin N))) (hK : IsCompact K)
    (hcap : ∀ᵐ z ∂μ, ∀ t : ℝ, |t| < r → X z + t • W z ∈ K) :
    Integrable (fun z => (1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients (X z) (W z)
      (A z) (A z) + g.inner (X z) (Z z) (A z)) μ ∧
      HasDerivAt (fun t : ℝ => ∫ z, (1 / 2 : ℝ) *
        g.inner (X z + t • W z) (A z + t • Z z) (A z + t • Z z) ∂μ)
        (∫ z, (1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients (X z) (W z)
          (A z) (A z) + g.inner (X z) (Z z) (A z) ∂μ) 0 := by
  have hG : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn
    (f := g.euclideanCoefficients) hG.continuous.continuousOn
  obtain ⟨D0, hD0⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ g.euclideanCoefficients)
    (hG.continuous_fderiv (by simp)).continuousOn
  let C := max C0 0
  let D := max D0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hD : 0 ≤ D := le_max_right _ _
  let F := fun (t : ℝ) (z : LoopPlane) => (1 / 2 : ℝ) *
    g.euclideanCoefficients (X z + t • W z) (A z + t • Z z) (A z + t • Z z)
  let F' := fun (t : ℝ) (z : LoopPlane) => (1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients
    (X z + t • W z) (W z) (A z + t • Z z) (A z + t • Z z) +
      g.euclideanCoefficients (X z + t • W z) (Z z) (A z + t • Z z)
  have hm (t : ℝ) : AEStronglyMeasurable (F t) μ := by
    have hY := hX.add (hW.const_smul t)
    have hP := hA.1.add (hZ.1.const_smul t)
    exact (ae_clm_apply (ae_clm_apply
      (hG.continuous.comp_aestronglyMeasurable hY) hP) hP).const_mul (1 / 2 : ℝ)
  have hm' : AEStronglyMeasurable (F' 0) μ := by
    have hfirst := ae_clm_apply (ae_clm_apply (ae_clm_apply
      ((hG.continuous_fderiv (by simp)).comp_aestronglyMeasurable hX) hW) hA.1) hA.1
    have hsecond := ae_clm_apply (ae_clm_apply
      (hG.continuous.comp_aestronglyMeasurable hX) hZ.1) hA.1
    simpa +instances only [F', zero_smul, add_zero, Pi.add_apply] using!
      (hfirst.const_mul (1 / 2 : ℝ)).add hsecond
  have hAsq := (memLp_two_iff_integrable_sq_norm hA.1).mp hA
  have hZsq := (memLp_two_iff_integrable_sq_norm hZ.1).mp hZ
  have hF0 : Integrable (F 0) μ := by
    apply (hAsq.const_mul ((1 / 2 : ℝ) * C)).mono' (hm 0)
    filter_upwards [hcap] with z hz
    have hzK : X z ∈ K := by simpa using hz 0 (by simpa using hr)
    have hbound : ‖g.euclideanCoefficients (X z)‖ ≤ C :=
      (hC0 (X z) hzK).trans (le_max_left _ _)
    have hn := (g.euclideanCoefficients (X z)).le_opNorm₂ (A z) (A z)
    calc
      ‖F 0 z‖ = (1 / 2 : ℝ) * ‖g.euclideanCoefficients (X z) (A z) (A z)‖ := by
        simp [F, norm_mul]
      _ ≤ (1 / 2 : ℝ) * (C * ‖A z‖ * ‖A z‖) :=
        mul_le_mul_of_nonneg_left (hn.trans (by gcongr)) (by norm_num)
      _ = _ := by ring
  let S : Set ℝ := {t | |t| < min r 1}
  have hS : S ∈ 𝓝 (0 : ℝ) := by
    apply (isOpen_lt continuous_abs continuous_const).mem_nhds
    change |(0 : ℝ)| < min r 1
    simpa only [abs_zero] using lt_min hr zero_lt_one
  obtain ⟨hi, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun z => (D * L + 2 * C) * (‖A z‖ ^ 2 + ‖Z z‖ ^ 2))
    hS (Eventually.of_forall hm) hF0 hm'
    (by
      filter_upwards [hcap, hWb] with z hz hw
      intro t ht
      have hzK := hz t (lt_of_lt_of_le ht (min_le_left _ _))
      exact quadratic_derivative_bound g _ _ _ _ hC hD hL
        ((hC0 _ hzK).trans (le_max_left _ _)) ((hD0 _ hzK).trans (le_max_left _ _))
        hw (le_trans ht.le (min_le_right _ _)))
    ((hAsq.add hZsq).const_mul (D * L + 2 * C))
    (ae_of_all _ fun z t _ => quadratic_hasDerivAt g (X z) (W z) (A z) (Z z) t)
  simp only [F', zero_smul, add_zero] at hi hd
  simpa +instances only [F, RiemannianMetric.euclideanCoefficients] using! And.intro hi hd

end PoincareConjecture.M65Euler
