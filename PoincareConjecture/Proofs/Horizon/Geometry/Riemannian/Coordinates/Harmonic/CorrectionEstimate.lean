import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.CoordinateEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Perturbation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts











noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ}


theorem integral_fderiv_apply_eq_zero
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, fderiv ℝ f x v) = 0 := by
  have hd : Integrable (fun x => fderiv ℝ f x v) volume :=
    (((hf.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfc.fderiv_apply ℝ v)
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (f := fun _ => (1 : ℝ)) (g := f) (v := v)
    (by
      simp only [fderiv_const_apply, zero_apply, zero_mul]
      exact integrable_zero _ _ _)
    (by simpa only [one_mul] using hd)
    (by simpa only [one_mul] using hf.continuous.integrable_of_hasCompactSupport hfc)
    (fun x _ => differentiableAt_const (𝕜 := ℝ) (x := x) (1 : ℝ))
    (fun x _ => hf.differentiable (by simp) x)
  simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul, integral_zero, neg_zero]
    using hparts

variable {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


def euclideanDivergenceOperator (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  g.pullbackVolumeDensity id x • (g.euclideanCoefficients x).inverse.comp B₀



theorem integral_inner_gradient_linear_eq_residual (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, g.inner x (D.gradient f x) (D.gradient (innerSL ℝ v) x) ∂g.volumeMeasure) =
      ∫ x, fderiv ℝ f x
        ((euclideanDivergenceOperator g x -
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v) := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := OpenPartialHomeomorph.refl E
  let ρ := g.pullbackVolumeDensity id
  let G : E → ℝ := fun x => g.inner x (D.gradient f x) (D.gradient (innerSL ℝ v) x)
  have hG : Continuous G := (D.contMDiff_inner_gradient
    (contMDiff_iff_contDiff.mpr hf)
    (contMDiff_iff_contDiff.mpr (innerSL ℝ v).contDiff)).continuous
  have hGc : HasCompactSupport G := D.hasCompactSupport_inner_gradient hfc _
  have hρ : Continuous ρ := continuous_iff_continuousAt.mpr fun x =>
    (g.contDiffAt_pullbackVolumeDensity contMDiffAt_id
      (by simpa using Function.injective_id)).1.continuousAt
  have hpull : chartPullback e G = G := by
    funext x
    simp [chartPullback, e]
    rfl
  have hint : (∫ x, G x ∂g.volumeMeasure) = ∫ x, G x * ρ x := by
    simpa only [hpull, show (e : E → E) = id from rfl] using
      integral_eq_chartPullback_density (g := g) e contMDiffOn_id contMDiffOn_id hG
        (by simp [e])
  have hmf (F : E → ℝ) (x : E) : mvfderiv (𝓡 n) F x = fderiv ℝ F x := by
    ext u
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  have hgrad (x : E) : D.gradient (innerSL ℝ v) x =
      (g.euclideanCoefficients x).inverse (innerSL ℝ v) := by
    unfold LeviCivitaData.gradient
    rw [hmf, ContinuousLinearMap.fderiv]
    rfl
  have hpoint (x : E) : G x * ρ x - fderiv ℝ f x v =
      fderiv ℝ f x ((euclideanDivergenceOperator g x -
        ContinuousLinearMap.id ℝ E) v) := by
    dsimp only [G]
    rw [D.inner_gradient, hmf, hgrad]
    simp only [euclideanDivergenceOperator, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      map_sub, map_smul, smul_eq_mul, ρ]
    change _ = g.pullbackVolumeDensity id x *
      fderiv ℝ f x ((g.euclideanCoefficients x).inverse (innerSL ℝ v)) - fderiv ℝ f x v
    exact congrArg (fun t : ℝ => t - fderiv ℝ f x v)
      (mul_comm (fderiv ℝ f x ((g.euclideanCoefficients x).inverse (innerSL ℝ v)))
        (g.pullbackVolumeDensity id x))
  have hGi : Integrable (fun x => G x * ρ x) volume :=
    (hG.mul hρ).integrable_of_hasCompactSupport hGc.mul_right
  have hdi : Integrable (fun x => fderiv ℝ f x v) volume :=
    (((hf.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfc.fderiv_apply ℝ v)
  change (∫ x, G x ∂g.volumeMeasure) = _
  rw [hint, ← sub_zero (∫ x, G x * ρ x), ← integral_fderiv_apply_eq_zero hf hfc v,
    ← integral_sub hGi hdi]
  exact integral_congr_ae (Eventually.of_forall hpoint)



theorem abs_integral_inner_gradient_linear_le (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (v : EuclideanSpace ℝ (Fin n)) {ε : ℝ}
    (hclose : ∀ x ∈ tsupport f,
      ‖euclideanDivergenceOperator g x -
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ ε) :
    |∫ x, g.inner x (D.gradient f x) (D.gradient (innerSL ℝ v) x) ∂g.volumeMeasure| ≤
      (ε * ‖v‖) * ∫ x, ‖fderiv ℝ f x‖ := by
  rw [integral_inner_gradient_linear_eq_residual D hf hfc v, ← Real.norm_eq_abs]
  have hdi : Integrable (fun x => ‖fderiv ℝ f x‖) volume :=
    ((hf.fderiv_right (m := ∞) (by simp)).continuous.norm).integrable_of_hasCompactSupport
      (hfc.fderiv ℝ).norm
  have hbound (x : EuclideanSpace ℝ (Fin n)) :
      ‖fderiv ℝ f x ((euclideanDivergenceOperator g x -
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v)‖ ≤
        (ε * ‖v‖) * ‖fderiv ℝ f x‖ := by
    by_cases hx : x ∈ tsupport f
    · calc
        _ ≤ ‖fderiv ℝ f x‖ * ‖(euclideanDivergenceOperator g x -
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v‖ :=
          (fderiv ℝ f x).le_opNorm _
        _ ≤ ‖fderiv ℝ f x‖ * (ε * ‖v‖) := by
          gcongr
          exact ((euclideanDivergenceOperator g x -
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).le_opNorm v).trans
              (mul_le_mul_of_nonneg_right (hclose x hx) (norm_nonneg v))
        _ = _ := mul_comm _ _
    · have hz : fderiv ℝ f x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (tsupport_fderiv_subset ℝ ht))
      simp only [hz, zero_apply, norm_zero, mul_zero, le_refl]
  simpa only [integral_const_mul] using
    norm_integral_le_of_norm_le (hdi.const_mul (ε * ‖v‖)) (Eventually.of_forall hbound)


theorem abs_integral_inner_gradient_coordinate_le (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (i : Fin n) {ε : ℝ}
    (hclose : ∀ x ∈ tsupport f,
      ‖euclideanDivergenceOperator g x -
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ ε) :
    |∫ x, g.inner x (D.gradient f x) (D.gradient (fun y => y i) x) ∂g.volumeMeasure| ≤
      ε * ∫ x, ‖fderiv ℝ f x‖ := by
  have hlinear : (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) :
      EuclideanSpace ℝ (Fin n) → ℝ) = fun x => x i := by
    funext x
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simpa only [hlinear, OrthonormalBasis.norm_eq_one, mul_one] using
    abs_integral_inner_gradient_linear_le D hf hfc
      (EuclideanSpace.basisFun (Fin n) ℝ i) hclose



theorem abs_integral_inner_gradient_linear_le_half_energy (D : LeviCivitaData g)
    {R a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 ≤ ε)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ z : EuclideanSpace ℝ (Fin n),
      a * ‖z‖ ^ 2 ≤ g.euclideanCoefficients x z z ∧
        g.euclideanCoefficients x z z ≤ b * ‖z‖ ^ 2)
    (hclose : ∀ x ∈ Metric.ball 0 R,
      ‖euclideanDivergenceOperator g x -
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ ε)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Metric.ball 0 R)
    (v : EuclideanSpace ℝ (Fin n)) :
    |∫ x, g.inner x (D.gradient f x) (D.gradient (innerSL ℝ v) x) ∂g.volumeMeasure| ≤
      (∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure) / 2 +
        (b / Real.sqrt (a ^ n)) * ε ^ 2 * ‖v‖ ^ 2 *
          volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / 2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let ρ := g.pullbackVolumeDensity id
  let G : E → ℝ := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  let B := b / Real.sqrt (a ^ n)
  let c := B * ε ^ 2 * ‖v‖ ^ 2 / 2
  have ha' : 0 < Real.sqrt (a ^ n) := Real.sqrt_pos.mpr (pow_pos ha n)
  have hB : 0 < B := div_pos hb ha'
  have hG : Continuous G := (D.contMDiff_inner_gradient
    (contMDiff_iff_contDiff.mpr hf) (contMDiff_iff_contDiff.mpr hf)).continuous
  have hGc : HasCompactSupport G := D.hasCompactSupport_inner_gradient hfc f
  have hGn (x : E) : 0 ≤ G x := by
    by_cases hz : D.gradient f x = 0
    · simp [G, hz]
    · exact (g.pos x _ hz).le
  have hρc : Continuous ρ := continuous_iff_continuousAt.mpr fun x =>
    (g.contDiffAt_pullbackVolumeDensity contMDiffAt_id
      (by simpa using Function.injective_id)).1.continuousAt
  have hGi : Integrable (fun x => G x * ρ x) volume :=
    (hG.mul hρc).integrable_of_hasCompactSupport hGc.mul_right
  have hint : (∫ x, G x ∂g.volumeMeasure) = ∫ x, G x * ρ x := by
    let e := OpenPartialHomeomorph.refl E
    have hpull : chartPullback e G = G := by
      funext x
      simp [chartPullback, e]
      rfl
    simpa only [hpull, show (e : E → E) = id from rfl] using
      integral_eq_chartPullback_density (g := g) e contMDiffOn_id contMDiffOn_id hG
        (by simp [e])
  have hci : Integrable ((Metric.ball (0 : E) R).indicator (fun _ => c)) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_const (C := c) measure_ball_ne_top)
  have hpoint (x : E) : (ε * ‖v‖) * ‖fderiv ℝ f x‖ ≤
      (G x * ρ x) / 2 + (Metric.ball (0 : E) R).indicator (fun _ => c) x := by
    by_cases hx : x ∈ Metric.ball 0 R
    · rw [Set.indicator_of_mem hx]
      have hdf := fderiv_sq_le_gradient_energy D f x hb.le (fun z => (hell x hx z).2)
      have hd := (g.pullbackVolumeDensity_id_bounds x ha (hell x hx)).1
      change Real.sqrt (a ^ n) ≤ ρ x at hd
      change ‖fderiv ℝ f x‖ ^ 2 ≤ b * G x at hdf
      have hs : ‖fderiv ℝ f x‖ ^ 2 ≤ B * (G x * ρ x) := by
        dsimp only [B]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ ha').mpr
        nlinarith [mul_le_mul_of_nonneg_left hdf ha'.le,
          mul_le_mul_of_nonneg_left hd (mul_nonneg hb.le (hGn x))]
      apply (mul_le_mul_iff_right₀ hB).mp
      dsimp only [c]
      nlinarith [sq_nonneg (‖fderiv ℝ f x‖ - B * ε * ‖v‖)]
    · have hdf : fderiv ℝ f x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hfs (tsupport_fderiv_subset ℝ ht)))
      have hzero : G x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hfs (D.tsupport_inner_gradient_subset_left f f ht)))
      simp only [hdf, hzero, norm_zero, mul_zero, zero_mul, zero_div,
        Set.indicator_of_notMem hx, add_zero, le_refl]
  have hi := integral_mono_of_nonneg
    (Eventually.of_forall fun x => mul_nonneg (mul_nonneg hε (norm_nonneg v)) (norm_nonneg _))
    ((hGi.div_const 2).add hci) (Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (hGi.div_const 2) hci, integral_div,
    ← hint, integral_indicator_const _ measurableSet_ball, smul_eq_mul] at hi
  have hres := abs_integral_inner_gradient_linear_le D hf hfc v
    (fun x hx => hclose x (hfs hx))
  have hc : volume.real (Metric.ball (0 : E) R) * c =
      B * ε ^ 2 * ‖v‖ ^ 2 * volume.real (Metric.ball (0 : E) R) / 2 := by
    dsimp only [c]
    ring
  rw [hc] at hi
  exact hres.trans hi



theorem weakPoisson_gradientEnergy_le_of_divergence_close (D : LeviCivitaData g)
    {R a b ε P : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 ≤ ε)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ z : EuclideanSpace ℝ (Fin n),
      a * ‖z‖ ^ 2 ≤ g.euclideanCoefficients x z z ∧
        g.euclideanCoefficients x z z ≤ b * ‖z‖ ^ 2)
    (hclose : ∀ x ∈ Metric.ball 0 R,
      ‖euclideanDivergenceOperator g x -
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ ε)
    (hP0 : 0 ≤ P) (hP : HasTestPoincare D (Metric.ball 0 R) P)
    (q : EnergyTest D (Set.univ : Set (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n))
    (hq : ∀ x ∈ Metric.ball 0 R, q x = inner ℝ v x) :
    gradientEnergy D (Metric.ball 0 R) (weakPoisson D (Metric.ball 0 R) hP0 hP q.laplacianLp)
        (weakPoisson D (Metric.ball 0 R) hP0 hP q.laplacianLp) ≤
      (b / Real.sqrt (a ^ n)) * ε ^ 2 * ‖v‖ ^ 2 *
        volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
  let Ω : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 R
  let c := (b / Real.sqrt (a ^ n)) * ε ^ 2 * ‖v‖ ^ 2 * volume.real Ω
  have hbound (u : H1Zero D Ω) :
      |gradientEnergy D Set.univ (q : H1Zero D Set.univ) (inclusion (subset_univ Ω) u)| ≤
        gradientEnergy D Ω u u / 2 + c / 2 := by
    induction u using UniformSpace.Completion.induction_on with
    | hp =>
      apply isClosed_le
      · fun_prop
      · fun_prop
    | ih f =>
      have heq : gradientEnergy D Set.univ (q : H1Zero D Set.univ)
          (inclusion (subset_univ Ω) (f : H1Zero D Ω)) =
          ∫ x, g.inner x (D.gradient f x) (D.gradient (innerSL ℝ v) x) ∂g.volumeMeasure := by
        rw [inclusion_coe, gradientEnergy_coe]
        apply integral_congr_ae
        filter_upwards [] with x
        change g.inner x (D.gradient q x) (D.gradient f x) = _
        rw [g.symm x (D.gradient q x) (D.gradient f x)]
        by_cases hx : x ∈ Ω
        · have hloc : (q : EuclideanSpace ℝ (Fin n) → ℝ) =ᶠ[𝓝 x] innerSL ℝ v := by
            filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
            exact hq y hy
          have hg : D.gradient q x = D.gradient (innerSL ℝ v) x := by
            unfold LeviCivitaData.gradient
            rw [Poincare.mvfderiv_eq_of_eventuallyEq hloc]
          rw [hg]
        · have hz (k : EuclideanSpace ℝ (Fin n) → ℝ) :
              g.inner x (D.gradient f x) (D.gradient k x) = 0 :=
            image_eq_zero_of_notMem_tsupport
              (f := fun y => g.inner y (D.gradient f y) (D.gradient k y))
              (fun ht => hx (f.support_subset (D.tsupport_inner_gradient_subset_left f k ht)))
          rw [hz, hz]
      rw [heq, gradientEnergy_coe]
      exact abs_integral_inner_gradient_linear_le_half_energy D ha hb hε hell hclose
        (contMDiff_iff_contDiff.mp f.smooth) f.hasCompactSupport f.support_subset v
  let w := weakPoisson D Ω hP0 hP q.laplacianLp
  have ho := weakPoisson_gradientEnergy_orthogonal (subset_univ Ω) hP0 hP q w
  change gradientEnergy D Set.univ ((q : H1Zero D Set.univ) + inclusion (subset_univ Ω) w)
    (inclusion (subset_univ Ω) w) = 0 at ho
  simp only [map_add, add_apply, gradientEnergy_inclusion] at ho
  have hcross : gradientEnergy D Set.univ (q : H1Zero D Set.univ)
      (inclusion (subset_univ Ω) w) = -gradientEnergy D Ω w w := by linarith
  have h := hbound w
  rw [hcross, abs_neg, abs_of_nonneg (gradientEnergy_self_nonneg w)] at h
  change gradientEnergy D Ω w w ≤ c
  linarith



theorem exists_weakHarmonicCoordinate_small_energy [NeZero n] (D : LeviCivitaData g)
    {R a b ε : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hε : 0 ≤ ε)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ z : EuclideanSpace ℝ (Fin n),
      a * ‖z‖ ^ 2 ≤ g.euclideanCoefficients x z z ∧
        g.euclideanCoefficients x z z ≤ b * ‖z‖ ^ 2)
    (hclose : ∀ x ∈ Metric.ball 0 R,
      ‖euclideanDivergenceOperator g x -
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ ε)
    (i : Fin n) :
    ∃ w : H1Zero D (Metric.ball 0 (R / 2)),
      (∀ f : EnergyTest D (Metric.ball 0 (R / 2)),
        (∫ x, (x i + (toL2 D (Metric.ball 0 (R / 2)) w) x) *
          D.laplacian f x ∂g.volumeMeasure) = 0) ∧
      gradientEnergy D (Metric.ball 0 (R / 2)) w w ≤
        (b / Real.sqrt (a ^ n)) * ε ^ 2 *
          volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2)) ∧
      ‖w‖ ^ 2 ≤ (Real.sqrt (b ^ n) * R ^ 2 * b / Real.sqrt (a ^ n) + 1) *
        ((b / Real.sqrt (a ^ n)) * ε ^ 2 *
          volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2))) := by
  obtain ⟨q, _, _, hq⟩ := exists_coordinate_cutoffs_energy (n := n) hR
  obtain ⟨hqsmooth, hqc, _, hqeq, _, _⟩ := hq i
  have hRhalf : 0 < R / 2 := by positivity
  have hballs : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 2) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  let P := Real.sqrt (b ^ n) * R ^ 2 * b / Real.sqrt (a ^ n)
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  have hP : HasTestPoincare D (Metric.ball 0 (R / 2)) P := by
    have htwice : 2 * (R / 2) = R := by ring
    simpa only [htwice] using
      metric_poincare_of_ellipticity D hRhalf ha hb.le (fun x hx => hell x (hballs hx))
  let qtest : EnergyTest D (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    ⟨q i, contMDiff_iff_contDiff.mpr hqsmooth, hqc, subset_univ _⟩
  let w := weakPoisson D (Metric.ball 0 (R / 2)) hP0 hP qtest.laplacianLp
  have hqlinear : ∀ x ∈ Metric.ball 0 (R / 2),
      qtest x = inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) x := by
    intro x hx
    change q i x = _
    rw [hqeq x hx]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  have henergy := weakPoisson_gradientEnergy_le_of_divergence_close D ha hb hε
    (fun x hx => hell x (hballs hx)) (fun x hx => hclose x (hballs hx)) hP0 hP
    qtest (EuclideanSpace.basisFun (Fin n) ℝ i) hqlinear
  simp only [OrthonormalBasis.norm_eq_one, one_pow, mul_one] at henergy
  have hweak : ∀ f : EnergyTest D (Metric.ball 0 (R / 2)),
      (∫ x, (q i x + (toL2 D (Metric.ball 0 (R / 2)) w) x) *
        D.laplacian f x ∂g.volumeMeasure) = 0 :=
    (isWeakHarmonicReplacement_iff_integral qtest w).mp
      (weakPoisson_isWeakHarmonicReplacement hP0 hP qtest)
  refine ⟨w, ?_, henergy, ?_⟩
  · intro f
    calc
      _ = ∫ x, (q i x + (toL2 D (Metric.ball 0 (R / 2)) w) x) *
          D.laplacian f x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Metric.ball 0 (R / 2)
        · rw [hqeq x hx]
        · have hz := D.laplacian_eq_zero_of_notMem_tsupport
            (f := (f : EuclideanSpace ℝ (Fin n) → ℝ))
            (fun ht => hx (f.support_subset ht))
          simp only [hz, mul_zero]
      _ = 0 := hweak f
  · exact (norm_sq_le_gradientEnergy hP w).trans
      (mul_le_mul_of_nonneg_left henergy (by positivity))

end PoincareConjecture.HarmonicCoordinates
