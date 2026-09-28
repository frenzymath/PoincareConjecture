import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.Energy
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.DensityBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.WeakDirichlet









noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


lemma fderiv_sq_le_gradient_energy (D : LeviCivitaData g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {B : ℝ} (hB : 0 ≤ B)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ B * ‖v‖ ^ 2) :
    ‖fderiv ℝ f x‖ ^ 2 ≤ B * g.inner x (D.gradient f x) (D.gradient f x) := by
  have hgn : 0 ≤ g.tangentNorm x (D.gradient f x) := Real.sqrt_nonneg _
  have hn (v : EuclideanSpace ℝ (Fin n)) :
      g.tangentNorm x v ≤ Real.sqrt B * ‖v‖ := by
    have h := Real.sqrt_le_sqrt (hupper v)
    simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul hB,
      Real.sqrt_sq (norm_nonneg v)] using h
  have hop : ‖fderiv ℝ f x‖ ≤ g.tangentNorm x (D.gradient f x) * Real.sqrt B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hgn (Real.sqrt_nonneg B))
    intro v
    have h := D.abs_mvfderiv_le_gradient_norm f x v
    have heq : mvfderiv (𝓡 n) f x v = fderiv ℝ f x v := by
      simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      rfl
    rw [heq] at h
    rw [Real.norm_eq_abs]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left (hn v) hgn])
  have hpos : 0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
    by_cases hz : D.gradient f x = 0
    · simp [hz]
    · exact (g.pos x _ hz).le
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hgn (Real.sqrt_nonneg B))).mpr hop
  simpa only [mul_pow, RiemannianMetric.tangentNorm, Real.sq_sqrt hpos,
    Real.sq_sqrt hB, mul_comm] using hs

open LeviCivitaData.Dirichlet



lemma gradient_energy_le_fderiv_sq (D : LeviCivitaData g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {a : ℝ} (ha : 0 < a)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v) :
    g.inner x (D.gradient f x) (D.gradient f x) ≤ ‖fderiv ℝ f x‖ ^ 2 / a := by
  let z : EuclideanSpace ℝ (Fin n) := D.gradient f x
  have hdual : g.inner x z z = fderiv ℝ f x z := by
    rw [show g.inner x z z = mvfderiv (𝓡 n) f x z from D.inner_gradient f x z]
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  have hbound : g.inner x z z ≤ ‖fderiv ℝ f x‖ * ‖z‖ := by
    rw [hdual]
    exact (le_abs_self _).trans ((fderiv ℝ f x).le_opNorm z)
  have hzn : ‖z‖ ≤ ‖fderiv ℝ f x‖ / a := by
    by_cases hz : z = 0
    · simp only [hz, norm_zero]
      positivity
    · have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      apply (le_div_iff₀ ha).mpr
      have h := (hlower z).trans hbound
      nlinarith
  calc
    _ ≤ ‖fderiv ℝ f x‖ * ‖z‖ := hbound
    _ ≤ ‖fderiv ℝ f x‖ * (‖fderiv ℝ f x‖ / a) :=
      mul_le_mul_of_nonneg_left hzn (norm_nonneg _)
    _ = _ := by ring



theorem integral_gradient_le_of_ellipticity (D : LeviCivitaData g)
    {R a b : ℝ} (ha : 0 < a)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {q : EuclideanSpace ℝ (Fin n) → ℝ} (hq : ContDiff ℝ ∞ q)
    (hqc : HasCompactSupport q) (hqs : tsupport q ⊆ Metric.ball 0 R) :
    (∫ x, g.inner x (D.gradient q x) (D.gradient q x) ∂g.volumeMeasure) ≤
      (Real.sqrt (b ^ n) / a) * ∫ x, ‖fderiv ℝ q x‖ ^ 2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := OpenPartialHomeomorph.refl E
  have heq : (e : E → E) = id := rfl
  let ρ := g.pullbackVolumeDensity id
  have hρ (x : E) : 0 < ρ x :=
    (g.contDiffAt_pullbackVolumeDensity contMDiffAt_id
      (by simpa using Function.injective_id)).2
  let G : E → ℝ := fun x => g.inner x (D.gradient q x) (D.gradient q x)
  have hG : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G :=
    D.contMDiff_inner_gradient (contMDiff_iff_contDiff.mpr hq) (contMDiff_iff_contDiff.mpr hq)
  have hGc : HasCompactSupport G := D.hasCompactSupport_inner_gradient hqc q
  have hGn (x : E) : 0 ≤ G x := by
    by_cases hz : D.gradient q x = 0
    · simp [G, hz]
    · exact (g.pos x _ hz).le
  have hpull : chartPullback e G = G := by
    funext x
    simp [chartPullback, e]
    rfl
  have hint : (∫ x, G x ∂g.volumeMeasure) = ∫ x, G x * ρ x := by
    simpa only [hpull, heq] using integral_eq_chartPullback_density (g := g) e
      contMDiffOn_id contMDiffOn_id hG.continuous (by simp [e])
  change (∫ x, G x ∂g.volumeMeasure) ≤ _
  rw [hint]
  have hdi : Integrable (fun x => ‖fderiv ℝ q x‖ ^ 2) volume :=
    (((hq.fderiv_right (m := ∞) (by simp)).continuous.norm).pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two] using
        ((hqc.fderiv ℝ).norm.mul_right : HasCompactSupport (fun x => ‖fderiv ℝ q x‖ * ‖fderiv ℝ q x‖)))
  have hpoint (x : E) : G x * ρ x ≤ (Real.sqrt (b ^ n) / a) * ‖fderiv ℝ q x‖ ^ 2 := by
    by_cases hx : x ∈ Metric.ball 0 R
    · have he := gradient_energy_le_fderiv_sq D q x ha (fun v => (hell x hx v).1)
      have hd := (g.pullbackVolumeDensity_id_bounds x ha (hell x hx)).2
      change G x ≤ ‖fderiv ℝ q x‖ ^ 2 / a at he
      change ρ x ≤ Real.sqrt (b ^ n) at hd
      calc
        _ ≤ (‖fderiv ℝ q x‖ ^ 2 / a) * Real.sqrt (b ^ n) :=
          mul_le_mul he hd (hρ x).le (by positivity)
        _ = _ := by ring
    · have hz : G x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hqs (D.tsupport_inner_gradient_subset_left q q ht)))
      rw [hz, zero_mul]
      positivity
  simpa only [integral_const_mul] using integral_mono_of_nonneg
    (Eventually.of_forall fun x => mul_nonneg (hGn x) (hρ x).le)
    (hdi.const_mul _) (Eventually.of_forall hpoint)



theorem integral_fderiv_sq_le_of_ellipticity (D : LeviCivitaData g)
    {R a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {q : EuclideanSpace ℝ (Fin n) → ℝ} (hq : ContDiff ℝ ∞ q)
    (hqc : HasCompactSupport q) (hqs : tsupport q ⊆ Metric.ball 0 R) :
    (∫ x, ‖fderiv ℝ q x‖ ^ 2) ≤ (b / Real.sqrt (a ^ n)) *
      ∫ x, g.inner x (D.gradient q x) (D.gradient q x) ∂g.volumeMeasure := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := OpenPartialHomeomorph.refl E
  let ρ := g.pullbackVolumeDensity id
  let G : E → ℝ := fun x => g.inner x (D.gradient q x) (D.gradient q x)
  have hc : 0 < Real.sqrt (a ^ n) := Real.sqrt_pos.mpr (pow_pos ha n)
  have hρ (x : E) : ContDiffAt ℝ ∞ ρ x ∧ 0 < ρ x :=
    g.contDiffAt_pullbackVolumeDensity contMDiffAt_id (by simpa using Function.injective_id)
  have hG : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ G := D.contMDiff_inner_gradient
    (contMDiff_iff_contDiff.mpr hq) (contMDiff_iff_contDiff.mpr hq)
  have hGn (x : E) : 0 ≤ G x := by
    by_cases hz : D.gradient q x = 0
    · simp [G, hz]
    · exact (g.pos x _ hz).le
  have hGc : HasCompactSupport G := D.hasCompactSupport_inner_gradient hqc q
  have hGi : Integrable (fun x => G x * ρ x) volume :=
    (hG.continuous.mul (continuous_iff_continuousAt.mpr fun x =>
      (hρ x).1.continuousAt)).integrable_of_hasCompactSupport hGc.mul_right
  have hpull : chartPullback e G = G := by
    funext x
    simp [chartPullback, e]
    rfl
  have hint : (∫ x, G x ∂g.volumeMeasure) = ∫ x, G x * ρ x := by
    simpa only [hpull, show (e : E → E) = id from rfl] using
      integral_eq_chartPullback_density (g := g) e contMDiffOn_id contMDiffOn_id
        hG.continuous (by simp [e])
  have hpoint (x : E) : Real.sqrt (a ^ n) * ‖fderiv ℝ q x‖ ^ 2 ≤ b * (G x * ρ x) := by
    by_cases hx : x ∈ Metric.ball 0 R
    · have hder := fderiv_sq_le_gradient_energy D q x hb (fun v => (hell x hx v).2)
      have hl := (g.pullbackVolumeDensity_id_bounds x ha (hell x hx)).1
      change Real.sqrt (a ^ n) ≤ ρ x at hl
      change ‖fderiv ℝ q x‖ ^ 2 ≤ b * G x at hder
      nlinarith [mul_le_mul_of_nonneg_left hder hc.le,
        mul_le_mul_of_nonneg_left hl (mul_nonneg hb (hGn x))]
    · have hz : fderiv ℝ q x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hqs (tsupport_fderiv_subset ℝ ht)))
      rw [hz, norm_zero, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg hb (mul_nonneg (hGn x) (hρ x).2.le)
  have h := integral_mono_of_nonneg
    (Eventually.of_forall fun x => mul_nonneg hc.le (sq_nonneg _))
    (hGi.const_mul b) (Eventually.of_forall hpoint)
  rw [integral_const_mul, integral_const_mul, ← hint] at h
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h)


lemma metric_poincare_of_density_bounds [NeZero n] (D : LeviCivitaData g)
    {R B c d : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (hc : 0 < c) (hd : 0 ≤ d)
    (hupper : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      g.inner x v v ≤ B * ‖v‖ ^ 2)
    (hdensity : ∀ x ∈ Metric.ball 0 R,
      c ≤ g.pullbackVolumeDensity id x ∧ g.pullbackVolumeDensity id x ≤ d)
    (f : EnergyTest D (Metric.ball 0 R)) :
    ‖testToL2 D (Metric.ball 0 R) f‖ ^ 2 ≤ (d * (2 * R) ^ 2 * B / c) *
      ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := OpenPartialHomeomorph.refl E
  let ρ := g.pullbackVolumeDensity id
  have heq : (e : E → E) = id := rfl
  have hρ (x : E) : ContDiffAt ℝ ∞ ρ x ∧ 0 < ρ x :=
    g.contDiffAt_pullbackVolumeDensity contMDiffAt_id (by simpa using Function.injective_id)
  have hρc : Continuous ρ := continuous_iff_continuousAt.mpr (fun x => (hρ x).1.continuousAt)
  have hpull (f : E → ℝ) : chartPullback e f = f := by
    funext x
    simp [chartPullback, e]
    rfl
  have hint (f : E → ℝ) (hf : Continuous f) :
      (∫ x, f x ∂g.volumeMeasure) = ∫ x, f x * ρ x := by
    simpa only [hpull, heq] using integral_eq_chartPullback_density (g := g) e
      contMDiffOn_id contMDiffOn_id hf (by simp [e])
  have hf : ContDiff ℝ ∞ (f : E → ℝ) := contMDiff_iff_contDiff.mp f.smooth
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
  have hpoint (x : E) : c * ‖fderiv ℝ (f : E → ℝ) x‖ ^ 2 ≤ B * (G x * ρ x) := by
    by_cases hx : x ∈ Metric.ball 0 R
    · have hder := fderiv_sq_le_gradient_energy D f x hB (hupper x hx)
      have hl := (hdensity x hx).1
      change c ≤ ρ x at hl
      change ‖fderiv ℝ (f : E → ℝ) x‖ ^ 2 ≤ B * G x at hder
      nlinarith [mul_le_mul_of_nonneg_left hder hc.le,
        mul_le_mul_of_nonneg_left hl (mul_nonneg hB (hGn x))]
    · have hz : fderiv ℝ (f : E → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun ht => hx (f.support_subset (tsupport_fderiv_subset ℝ ht)))
      rw [hz, norm_zero, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg hB (mul_nonneg (hGn x) (hρ x).2.le)
  have hgrad := integral_mono_of_nonneg
    (Eventually.of_forall fun x => mul_nonneg hc.le (sq_nonneg _))
    (hGi.const_mul B) (Eventually.of_forall hpoint)
  rw [integral_const_mul, integral_const_mul, ← hint G hG.continuous] at hgrad
  have hgrad' : (∫ x, ‖fderiv ℝ (f : E → ℝ) x‖ ^ 2) ≤
      B / c * ∫ x, G x ∂g.volumeMeasure := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hgrad)
  have hvol : (∫ x, f x ^ 2 ∂g.volumeMeasure) ≤ d * ∫ x, f x ^ 2 := by
    rw [hint (fun x => f x ^ 2) (by fun_prop)]
    have hpoint' (x : E) : f x ^ 2 * ρ x ≤ d * f x ^ 2 := by
      by_cases hx : x ∈ Metric.ball 0 R
      · have hu := (hdensity x hx).2
        change ρ x ≤ d at hu
        nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg (f x))]
      · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (f.support_subset ht))
        simp [hz]
    simpa only [integral_const_mul] using integral_mono_of_nonneg
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hρ x).2.le)
      (hfi.const_mul d) (Eventually.of_forall hpoint')
  have hp := integral_sq_le_fderiv_sq_of_support_ball hR hf f.hasCompactSupport
    ((subset_tsupport (f : E → ℝ)).trans f.support_subset)
  calc
    ‖testToL2 D (Metric.ball 0 R) f‖ ^ 2 = ∫ x, f x ^ 2 ∂g.volumeMeasure := by
      rw [← real_inner_self_eq_norm_sq, testToL2_inner]
      simp only [pow_two]
    _ ≤ d * ∫ x, f x ^ 2 := hvol
    _ ≤ d * ((2 * R) ^ 2 * ∫ x, ‖fderiv ℝ (f : E → ℝ) x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hp hd
    _ ≤ d * ((2 * R) ^ 2 * (B / c * ∫ x, G x ∂g.volumeMeasure)) := by
      gcongr
    _ = _ := by dsimp [G]; ring



theorem metric_poincare_of_ellipticity [NeZero n] (D : LeviCivitaData g)
    {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 ≤ b)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) :
    HasTestPoincare D (Metric.ball 0 R)
      (Real.sqrt (b ^ n) * (2 * R) ^ 2 * b / Real.sqrt (a ^ n)) := by
  intro f
  exact metric_poincare_of_density_bounds D hR hb (Real.sqrt_pos.mpr (pow_pos ha n))
    (Real.sqrt_nonneg _) (fun x hx v => (hell x hx v).2)
    (fun x hx => g.pullbackVolumeDensity_id_bounds x ha (hell x hx)) f



theorem exists_weakDirichlet_of_ellipticity [NeZero n] (D : LeviCivitaData g)
    {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 ≤ b)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    (ell : H1Zero D (Metric.ball 0 R) →L[ℝ] ℝ) :
    ∃ w : H1Zero D (Metric.ball 0 R),
      (∀ v, gradientEnergy D (Metric.ball 0 R) w v = ell v) ∧
      ‖w‖ ≤ (Real.sqrt (b ^ n) * (2 * R) ^ 2 * b / Real.sqrt (a ^ n) + 1) * ‖ell‖ := by
  have hP := metric_poincare_of_ellipticity D hR ha hb hell
  have hP0 : 0 ≤ Real.sqrt (b ^ n) * (2 * R) ^ 2 * b / Real.sqrt (a ^ n) := by positivity
  exact ⟨weakDirichlet D (Metric.ball 0 R) hP0 hP ell,
    weakDirichlet_spec hP0 hP ell, norm_weakDirichlet_apply_le hP0 hP ell⟩

end PoincareConjecture.HarmonicCoordinates
