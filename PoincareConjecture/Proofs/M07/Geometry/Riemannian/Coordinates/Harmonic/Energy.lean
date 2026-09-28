import PoincareConjecture.Proofs.M07.Analysis.Sobolev.Euclidean.Translation
import PoincareConjecture.Proofs.M07.Analysis.Sobolev.Euclidean.L2
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Heat.Dirichlet.Compactness.ChartEnergy

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ} [NeZero n]

lemma eLpNorm_le_of_support_ball {R : ℝ} (hR : 0 < R)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : Function.support f ⊆ Metric.ball 0 R) :
    eLpNorm f p volume ≤ ENNReal.ofReal (2 * R) *
      eLpNorm (fun x => ‖fderiv ℝ f x‖) p volume := by
  let v := EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n)
  let a := (2 * R) • v
  have ha : ‖a‖ = 2 * R := by
    simp only [a, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * R),
      v, OrthonormalBasis.norm_eq_one, mul_one]
  have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ 0) : f (x - a) = 0 := by
    by_contra hne
    have hxR : ‖x‖ < R := by simpa using hs hx
    have hyR : ‖x - a‖ < R := by simpa using hs hne
    have ht : ‖a‖ ≤ ‖x‖ + ‖x - a‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le x (x - a)
    rw [ha] at ht
    linarith
  calc
    _ ≤ eLpNorm (fun x => f x - f (x - a)) p volume := by
      apply eLpNorm_mono
      intro x
      by_cases hx : f x = 0
      · simp only [hx, norm_zero, zero_sub, norm_neg, norm_nonneg]
      · rw [hzero x hx, sub_zero]
    _ ≤ ENNReal.ofReal ‖a‖ * eLpNorm (fun x => ‖fderiv ℝ f x‖) p volume :=
      Poincare.Analysis.Sobolev.eLpNorm_translate_sub_le_smul_eLpNorm_fderiv
        hp hptop (hf.of_le (by simp)) a
    _ = _ := by rw [ha]

lemma integral_sq_le_fderiv_sq_of_support_ball {R : ℝ} (hR : 0 < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : Function.support f ⊆ Metric.ball 0 R) :
    (∫ x, f x ^ 2) ≤ (2 * R) ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  have hfl : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hc
  have hd : Continuous (fun x => ‖fderiv ℝ f x‖) :=
    (hf.fderiv_right (m := ∞) (by simp)).continuous.norm
  have hdl : MemLp (fun x => ‖fderiv ℝ f x‖) 2 volume :=
    hd.memLp_of_hasCompactSupport (hc.fderiv ℝ).norm
  have he := eLpNorm_le_of_support_ball hR (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num) hf hs
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    hdl.eLpNorm_lt_top.ne) he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * R)] at hreal
  have hsquare := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity)).mpr hreal
  simpa only [mul_pow, Poincare.Analysis.Sobolev.eLpNorm_toReal_sq_eq_integral hfl,
    Poincare.Analysis.Sobolev.eLpNorm_toReal_sq_eq_integral hdl] using hsquare

open LeviCivitaData.Dirichlet

lemma exists_metric_poincare_on_ball
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ f : EnergyTest D (Metric.ball 0 R),
      ‖testToL2 D (Metric.ball 0 R) f‖ ^ 2 ≤ P *
        ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := OpenPartialHomeomorph.refl E
  let K := Metric.closedBall (0 : E) R
  let ρ := g.pullbackVolumeDensity id
  have heq : (e : E → E) = id := rfl
  have hK : IsCompact K := isCompact_closedBall 0 R
  have hρ (x : E) : ContDiffAt ℝ ∞ ρ x ∧ 0 < ρ x :=
    g.contDiffAt_pullbackVolumeDensity contMDiffAt_id (by simpa using Function.injective_id)
  have hρc : Continuous ρ := continuous_iff_continuousAt.mpr (fun x => (hρ x).1.continuousAt)
  obtain ⟨c, hc, hlower⟩ := hK.exists_forall_le'
    hρc.continuousOn (fun x _ => (hρ x).2)
  obtain ⟨B, hB⟩ := hK.bddAbove_image hρc.continuousOn
  let b := max B 0
  have hb : 0 ≤ b := le_max_right _ _
  have hupper (x : E) (hx : x ∈ K) : ρ x ≤ b :=
    (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hpull (f : E → ℝ) : chartPullback e f = f := by
    funext x
    simp [chartPullback, e]
    rfl
  obtain ⟨A, hA, hder⟩ := exists_chart_fderiv_sq_bound (D := D) e contMDiffOn_id
    hK (by simp [e])
  have hdensity (f : E → ℝ) (hf : Continuous f) :
      (∫ x, f x ∂g.volumeMeasure) = ∫ x, f x * ρ x := by
    simpa only [hpull, heq] using integral_eq_chartPullback_density (g := g) e
      contMDiffOn_id contMDiffOn_id hf (by simp [e])
  refine ⟨b * (2 * R) ^ 2 * A / c, by positivity, ?_⟩
  intro f
  have hf : ContDiff ℝ ∞ (f : E → ℝ) := contMDiff_iff_contDiff.mp f.smooth
  have hs : tsupport (f : E → ℝ) ⊆ K :=
    f.support_subset.trans Metric.ball_subset_closedBall
  let G : E → ℝ := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  have hG : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G := D.contMDiff_inner_gradient f.smooth f.smooth
  have hGc : HasCompactSupport G := D.hasCompactSupport_inner_gradient f.hasCompactSupport f
  have hGn (x : E) : 0 ≤ G x := by
    by_cases hz : D.gradient f x = 0
    · simp [G, hz]
    · exact (g.pos x _ hz).le
  have hGi : Integrable (fun x => G x * ρ x) volume :=
    (hG.continuous.mul hρc).integrable_of_hasCompactSupport hGc.mul_right
  have hfi : Integrable (fun x => f x ^ 2) volume :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two] using
        (f.hasCompactSupport.mul_right : HasCompactSupport (fun x => f x * f x)))
  have hpoint (x : E) : c * ‖fderiv ℝ (f : E → ℝ) x‖ ^ 2 ≤ A * (G x * ρ x) := by
    by_cases hx : x ∈ K
    · have hd : ‖fderiv ℝ (f : E → ℝ) x‖ ^ 2 ≤ A * G x := by
        have hd := hder f f.smooth x hx
        rw [hpull] at hd
        exact hd
      have hl := hlower x hx
      nlinarith [mul_le_mul_of_nonneg_left hd hc.le,
        mul_le_mul_of_nonneg_left hl (mul_nonneg hA (hGn x))]
    · have hz : fderiv ℝ (f : E → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun ht => hx (hs (tsupport_fderiv_subset ℝ ht)))
      rw [hz, norm_zero, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg hA (mul_nonneg (hGn x) (hρ x).2.le)
  have hgrad := integral_mono_of_nonneg
    (Eventually.of_forall fun x => mul_nonneg hc.le (sq_nonneg _))
    (hGi.const_mul A) (Eventually.of_forall hpoint)
  rw [integral_const_mul, integral_const_mul, ← hdensity G hG.continuous] at hgrad
  have hgrad' : (∫ x, ‖fderiv ℝ (f : E → ℝ) x‖ ^ 2) ≤
      A / c * ∫ x, G x ∂g.volumeMeasure := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hgrad)
  have hvol : (∫ x, f x ^ 2 ∂g.volumeMeasure) ≤ b * ∫ x, f x ^ 2 := by
    rw [hdensity (fun x => f x ^ 2) (by fun_prop)]
    have hpoint' (x : E) : f x ^ 2 * ρ x ≤ b * f x ^ 2 := by
      by_cases hx : x ∈ K
      · nlinarith [mul_le_mul_of_nonneg_left (hupper x hx) (sq_nonneg (f x))]
      · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
        simp [hz]
    simpa only [integral_const_mul] using integral_mono_of_nonneg
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hρ x).2.le)
      (hfi.const_mul b) (Eventually.of_forall hpoint')
  have hp := integral_sq_le_fderiv_sq_of_support_ball hR hf f.hasCompactSupport
    ((subset_tsupport (f : E → ℝ)).trans f.support_subset)
  calc
    ‖testToL2 D (Metric.ball 0 R) f‖ ^ 2 = ∫ x, f x ^ 2 ∂g.volumeMeasure := by
      rw [← real_inner_self_eq_norm_sq, testToL2_inner]
      simp only [pow_two]
    _ ≤ b * ∫ x, f x ^ 2 := hvol
    _ ≤ b * ((2 * R) ^ 2 * ∫ x, ‖fderiv ℝ (f : E → ℝ) x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hp hb
    _ ≤ b * ((2 * R) ^ 2 * (A / c * ∫ x, G x ∂g.volumeMeasure)) := by
      gcongr
    _ = _ := by dsimp [G]; ring

end PoincareConjecture.HarmonicCoordinates
