import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaVariationalComparison
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Uniformity
open scoped Manifold ContDiff Topology Bundle BoundedContinuousFunction ENNReal

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace M60

def suAlphaDerivativePair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : LoopPlane → E) (z : LoopPlane) : E × E :=
  (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ 0),
    fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ 1))

theorem suAlphaDerivativePair_blend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {rho : LoopPlane → ℝ} {u v : LoopPlane → E} {z : LoopPlane}
    (hrho : DifferentiableAt ℝ rho z) (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    suAlphaDerivativePair (fun y => (1 - rho y) • u y + rho y • v y) z =
      (1 - rho z) • suAlphaDerivativePair u z + rho z • suAlphaDerivativePair v z +
        (fderiv ℝ rho z (EuclideanSpace.basisFun (Fin 2) ℝ 0) • (v z - u z),
          fderiv ℝ rho z (EuclideanSpace.basisFun (Fin 2) ℝ 1) • (v z - u z)) := by
  have hd := ((hrho.hasFDerivAt.const_sub 1).smul hu.hasFDerivAt).add
    (hrho.hasFDerivAt.smul hv.hasFDerivAt)
  have hderiv : fderiv ℝ (fun y => (1 - rho y) • u y + rho y • v y) z =
      (1 - rho z) • fderiv ℝ u z + (-fderiv ℝ rho z).smulRight (u z) +
        (rho z • fderiv ℝ v z + (fderiv ℝ rho z).smulRight (v z)) := hd.fderiv
  unfold suAlphaDerivativePair
  rw [hderiv]
  ext <;> simp only [add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    neg_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  all_goals module

theorem suSphereChart_target (p : UnitTwoSphere) :
    (chartAt LoopPlane p).target = univ := by
  let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
  change (stereographic' 2 (-p)).target = univ
  simp

theorem suSphereChart_smooth (p : UnitTwoSphere) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (chartAt LoopPlane p).symm :=
  contMDiffOn_univ.mp (suSphereChart_target p ▸ contMDiffOn_chart_symm (I := 𝓡 2))

theorem suSphereChart_inner (p : UnitTwoSphere) (z v w : LoopPlane) :
    m60RoundSphereMetric.inner ((chartAt LoopPlane p).symm z)
      (mfderiv (𝓡 2) (𝓡 2) (chartAt LoopPlane p).symm z v)
      (mfderiv (𝓡 2) (𝓡 2) (chartAt LoopPlane p).symm z w) =
        (16 / (‖z‖ ^ 2 + 4) ^ 2) * inner ℝ v w :=
  M36.sphere_chart_differential_inner_at p z v w

theorem suSphereChart_volumeDensity (p : UnitTwoSphere) (z : LoopPlane) :
    m60RoundSphereMetric.pullbackVolumeDensity (chartAt LoopPlane p).symm z =
      16 / (‖z‖ ^ 2 + 4) ^ 2 := by
  unfold RiemannianMetric.pullbackVolumeDensity
  have hgram : (Matrix.of (fun i j : Fin 2 =>
      m60RoundSphereMetric.inner ((chartAt LoopPlane p).symm z)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt LoopPlane p).symm z
          (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 2) (chartAt LoopPlane p).symm z
          (EuclideanSpace.basisFun (Fin 2) ℝ j)))) =
      Matrix.diagonal (fun _ : Fin 2 => 16 / (‖z‖ ^ 2 + 4) ^ 2) := by
    ext i j
    simp only [Matrix.of_apply, suSphereChart_inner, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]
  rw [hgram, Matrix.det_diagonal, Fin.prod_univ_two, Real.sqrt_mul_self (by positivity)]

theorem suSphereChart_integral (p : UnitTwoSphere)
    (phi : UnitTwoSphere → ℝ) (hphi : Continuous phi) :
    (∫ x, phi x ∂m60RoundSphereMetric.volumeMeasure) =
      ∫ z : LoopPlane, phi ((chartAt LoopPlane p).symm z) *
        (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  have hs : (chartAt LoopPlane p).source = {-p}ᶜ := by
    let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
    change (stereographic' 2 (-p)).source = {-p}ᶜ
    simp
  have hnull : m60RoundSphereMetric.volumeMeasure ((chartAt LoopPlane p).source)ᶜ = 0 := by
    rw [hs, compl_compl]
    exact m60RoundSphereMetric_volume_singleton _
  have hi := m60RoundSphereMetric.integral_target_eq_integral_pullback_density
    (chartAt LoopPlane p).symm contMDiffOn_chart_symm contMDiffOn_chart hphi.continuousOn
  have hae : ∀ᵐ x ∂m60RoundSphereMetric.volumeMeasure, x ∈ (chartAt LoopPlane p).source := by
    rw [ae_iff]
    exact hnull
  change (∫ x in (chartAt LoopPlane p).source, phi x
      ∂m60RoundSphereMetric.volumeMeasure) =
    ∫ z in (chartAt LoopPlane p).target, phi ((chartAt LoopPlane p).symm z) *
      m60RoundSphereMetric.pullbackVolumeDensity (chartAt LoopPlane p).symm z at hi
  rw [← integral_eq_setIntegral hae phi, suSphereChart_target,
    setIntegral_univ] at hi
  simpa only [suSphereChart_volumeDensity] using hi

theorem suSphereChart_integrable (p : UnitTwoSphere)
    (phi : UnitTwoSphere → ℝ) (hphi : Continuous phi) :
    Integrable (fun z : LoopPlane => phi ((chartAt LoopPlane p).symm z) *
      (16 / (‖z‖ ^ 2 + 4) ^ 2)) := by
  obtain ⟨C, hC⟩ := (isCompact_range hphi).isBounded.exists_norm_le
  have hfactor : Continuous (fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2) :=
    continuous_const.div₀ (((continuous_norm.pow 2).add continuous_const).pow 2)
      (fun _ => by positivity)
  apply (m60SphereParameter_factor_integrable.const_mul C).mono'
    ((hphi.comp (suSphereChart_smooth p).continuous).mul hfactor).aestronglyMeasurable
  filter_upwards [] with z
  change ‖phi ((chartAt LoopPlane p).symm z) * (16 / (‖z‖ ^ 2 + 4) ^ 2)‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ 16 / (‖z‖ ^ 2 + 4) ^ 2 by positivity)]
  exact mul_le_mul_of_nonneg_right (hC _ (mem_range_self _)) (by positivity)

theorem suSphereChart_energy
    (g : RiemannianMetric n M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (p : UnitTwoSphere) (z : LoopPlane) :
    m60EnergyDensity g (f ∘ (chartAt LoopPlane p).symm) z =
      m60SphereIntrinsicEnergy g f ((chartAt LoopPlane p).symm z) *
        (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type) :=
    ⟨m60RoundSphereMetric.toRiemannianMetric⟩
  let q := (chartAt LoopPlane p).symm z
  let w := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 2) (chartAt LoopPlane p).symm z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let B := (metricPullbackForm (n := 2) g f q).toBilinForm
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) q) := by
    unfold TangentSpace
    infer_instance
  have hw (i j : Fin 2) : inner ℝ (w i) (w j) =
      (16 / (‖z‖ ^ 2 + 4) ^ 2) * (if i = j then 1 else 0) := by
    change m60RoundSphereMetric.inner q (w i) (w j) = _
    rw [suSphereChart_inner, (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_ite]
  have htrace := sum_bilinear_conformal_basis B
    (m60RoundSphereMetric.orthonormalBasis q) w
    (by change 2 = Module.finrank ℝ LoopPlane; simp) (by positivity) hw
  have hleft : m60EnergyDensity g (f ∘ (chartAt LoopPlane p).symm) z =
      (1 / 2 : ℝ) * ∑ i, B (w i) (w i) := by
    unfold m60EnergyDensity
    rw [Matrix.trace_fin_two]
    unfold m60AreaGram
    rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
      ((suSphereChart_smooth p).mdifferentiable (by simp) _)]
    simp only [B, ContinuousLinearMap.toBilinForm_apply, metricPullbackForm_apply,
      w, q, Fin.sum_univ_two]
    rfl
  rw [hleft, htrace]
  simp only [B, ContinuousLinearMap.toBilinForm_apply, metricPullbackForm_apply,
    m60SphereIntrinsicEnergy, q]
  ring

def suSphereChartAlphaDensity
    (g : RiemannianMetric n M) (alpha : ℝ) (p : UnitTwoSphere)
    (f : UnitTwoSphere → M) (z : LoopPlane) : ℝ :=
  (1 + 2 * m60EnergyDensity g (f ∘ (chartAt LoopPlane p).symm) z /
    (16 / (‖z‖ ^ 2 + 4) ^ 2)) ^ alpha * (16 / (‖z‖ ^ 2 + 4) ^ 2)

theorem suSphereChartAlphaDensity_eq_coefficients
    (g : RiemannianMetric n M) (alpha : ℝ) (p : UnitTwoSphere) (b : M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (z : LoopPlane)
    (hz : f ((chartAt LoopPlane p).symm z) ∈ (extChartAt (𝓡 n) b).source) :
    let c := extChartAt (𝓡 n) b
    let u := c ∘ f ∘ (chartAt LoopPlane p).symm
    suSphereChartAlphaDensity g alpha p f z =
      (1 + (∑ i : Fin 2, g.pullbackCoefficients c.symm (u z)
        (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))) /
          (16 / (‖z‖ ^ 2 + 4) ^ 2)) ^ alpha * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  dsimp only
  rw [suSphereChartAlphaDensity, m60EnergyDensity_eq_chart g b
    ((hf.comp (suSphereChart_smooth p)).mdifferentiable (by simp) z) hz]
  simp only [Function.comp_apply]
  congr 2
  ring

theorem suSphereChartAlphaDensity_eq_regularized
    (g : RiemannianMetric n M) (alpha : ℝ) (p : UnitTwoSphere) (b : M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (z : LoopPlane)
    (hz : f ((chartAt LoopPlane p).symm z) ∈ (extChartAt (𝓡 n) b).source) :
    let u := (extChartAt (𝓡 n) b) ∘ f ∘ (chartAt LoopPlane p).symm
    let B := suAlphaPairMetric (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (u z))
    let lambda := 16 / (‖z‖ ^ 2 + 4) ^ 2
    suSphereChartAlphaDensity g alpha p f z =
      lambda ^ (1 - alpha) * suRegularizedQuadratic B lambda alpha (suAlphaDerivativePair u z) := by
  let u := (extChartAt (𝓡 n) b) ∘ f ∘ (chartAt LoopPlane p).symm
  let B := suAlphaPairMetric (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (u z))
  let q := B (suAlphaDerivativePair u z) (suAlphaDerivativePair u z)
  let lambda : ℝ := 16 / (‖z‖ ^ 2 + 4) ^ 2
  have hl : 0 < lambda := by dsimp only [lambda]; positivity
  have hq : 0 ≤ q := by
    have h := m60EnergyDensity_nonneg g (f ∘ (chartAt LoopPlane p).symm) z
    rw [m60EnergyDensity_eq_chart g b
      ((hf.comp (suSphereChart_smooth p)).mdifferentiable (by simp) z) hz] at h
    simp only [Fin.sum_univ_two, Function.comp_apply] at h
    change 0 ≤ (1 / 2 : ℝ) * q at h
    linarith
  rw [suSphereChartAlphaDensity_eq_coefficients g alpha p b f hf z hz]
  simp only [Fin.sum_univ_two]
  change (1 + q / lambda) ^ alpha * lambda = lambda ^ (1 - alpha) * (lambda + q) ^ alpha
  rw [one_add_div hl.ne', Real.div_rpow (add_nonneg hl.le hq) hl.le,
    Real.rpow_sub hl, Real.rpow_one]
  ring

theorem suSphereChartAlphaDensity_integral
    (g : RiemannianMetric n M) {alpha : ℝ} (ha : 0 ≤ alpha) (p : UnitTwoSphere)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    Integrable (suSphereChartAlphaDensity g alpha p f) ∧
      m60SphereAlphaEnergy g alpha f = ∫ z, suSphereChartAlphaDensity g alpha p f z := by
  let P : UnitTwoSphere → ℝ := fun q => (1 + 2 * m60SphereIntrinsicEnergy g f q) ^ alpha
  have hP : Continuous P := (Real.continuous_rpow_const ha).comp
    (continuous_const.add (continuous_const.mul
      (m60SphereIntrinsicEnergy_contMDiff g f hf).continuous))
  have heq : suSphereChartAlphaDensity g alpha p f =
      fun z => P ((chartAt LoopPlane p).symm z) * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
    funext z
    dsimp only [suSphereChartAlphaDensity, P]
    rw [suSphereChart_energy g f (hf.of_le (by simp)) p z]
    congr 2
    field_simp
  rw [heq]
  exact ⟨suSphereChart_integrable p P hP, suSphereChart_integral p P hP⟩

theorem suSphereChart_observedLp_bound
    [CompactSpace M] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : RiemannianMetric n M) (e : M → F)
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ e) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ alpha : ℝ, 1 ≤ alpha →
      ∀ (f : UnitTwoSphere → M), ContMDiff (𝓡 2) (𝓡 n) ∞ f → ∀ p : UnitTwoSphere,
        MemLp (fun z => fderiv ℝ (e ∘ f ∘ (chartAt LoopPlane p).symm) z)
          (ENNReal.ofReal (2 * alpha)) volume ∧
        (eLpNorm (fun z => fderiv ℝ (e ∘ f ∘ (chartAt LoopPlane p).symm) z)
          (ENNReal.ofReal (2 * alpha)) volume).toReal ≤
            (B ^ alpha * m60SphereAlphaEnergy g alpha f) ^ (2 * alpha)⁻¹ ∧
        (∫ z, ‖fderiv ℝ (e ∘ f ∘ (chartAt LoopPlane p).symm) z‖ ^ (2 * alpha)) ≤
          B ^ alpha * m60SphereAlphaEnergy g alpha f := by
  obtain ⟨B, hB, hb⟩ := exists_observed_derivative_energy_bound g e (he.of_le (by simp))
  refine ⟨4 * B, by positivity, fun alpha ha f hf p => ?_⟩
  let u := e ∘ f ∘ (chartAt LoopPlane p).symm
  let P : UnitTwoSphere → ℝ := fun q => (1 + 2 * m60SphereIntrinsicEnergy g f q) ^ alpha
  let Q : LoopPlane → ℝ := fun z => P ((chartAt LoopPlane p).symm z) *
    (16 / (‖z‖ ^ 2 + 4) ^ 2)
  have ha0 : 0 ≤ alpha := by linarith
  have hap : 0 < 2 * alpha := by linarith
  have hu : ContDiff ℝ ∞ u :=
    contMDiff_iff_contDiff.mp (he.comp (hf.comp (suSphereChart_smooth p)))
  have hdc := hu.continuous_fderiv (by simp)
  have hP : Continuous P := (Real.continuous_rpow_const ha0).comp
    (continuous_const.add (continuous_const.mul
      (m60SphereIntrinsicEnergy_contMDiff g f hf).continuous))
  have hQ : Integrable Q := suSphereChart_integrable p P hP
  have hpoint (z : LoopPlane) : ‖fderiv ℝ u z‖ ^ (2 * alpha) ≤ (4 * B) ^ alpha * Q z := by
    have hcomp := (hf.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).comp
      ((suSphereChart_smooth p).of_le (by simp))
    have h0 := hb (f ∘ (chartAt LoopPlane p).symm) hcomp z 0
    have h1 := hb (f ∘ (chartAt LoopPlane p).symm) hcomp z 1
    have hsquare : ‖fderiv ℝ u z‖ ^ 2 ≤
        (4 * B) * (m60SphereIntrinsicEnergy g f ((chartAt LoopPlane p).symm z) *
          (16 / (‖z‖ ^ 2 + 4) ^ 2)) := by
      rw [← suSphereChart_energy g f (hf.of_le (by simp)) p z]
      have h := plane_opNorm_sq_le (fderiv ℝ u z)
      linarith
    have hfactor : 16 / (‖z‖ ^ 2 + 4) ^ 2 ≤ (1 : ℝ) := by
      apply (div_le_one (by positivity)).mpr
      nlinarith [sq_nonneg ‖z‖]
    have hr := suAlpha_coercivity_rpow (norm_nonneg _) (by positivity) (by positivity)
      hfactor (m60SphereIntrinsicEnergy_nonneg g f _) ha hsquare
    simpa only [Q, P, mul_assoc] using hr
  have hint : Integrable (fun z => ‖fderiv ℝ u z‖ ^ (2 * alpha)) :=
    (hQ.const_mul ((4 * B) ^ alpha)).mono'
      ((Real.continuous_rpow_const hap.le).comp hdc.norm).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact hpoint z)
  have hp : MemLp (fun z => fderiv ℝ u z) (ENNReal.ofReal (2 * alpha)) volume := by
    apply (integrable_norm_rpow_iff hdc.aestronglyMeasurable
      (ENNReal.ofReal_pos.mpr hap).ne' ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hap.le] using hint
  have hi : (∫ z, ‖fderiv ℝ u z‖ ^ (2 * alpha)) ≤
      (4 * B) ^ alpha * m60SphereAlphaEnergy g alpha f := by
    calc
      _ ≤ ∫ z, (4 * B) ^ alpha * Q z :=
        integral_mono hint (hQ.const_mul _) hpoint
      _ = _ := by
        rw [integral_const_mul, ← suSphereChart_integral p P hP]
        rfl
  refine ⟨hp, ?_, hi⟩
  change (eLpNorm (fun z => fderiv ℝ u z) (ENNReal.ofReal (2 * alpha)) volume).toReal ≤ _
  rw [hp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hap).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hap.le,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun z =>
      Real.rpow_nonneg (norm_nonneg _) _) _)]
  exact Real.rpow_le_rpow (integral_nonneg fun z =>
    Real.rpow_nonneg (norm_nonneg _) _) hi (inv_nonneg.mpr hap.le)

theorem suAlpha_observed_equicontinuous
    [CompactSpace M] (g : RiemannianMetric n M) (e : M → ℝ)
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ e) {alpha C : ℝ} (ha : 1 < alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C) :
    Equicontinuous (fun j => e ∘ f j) := by
  obtain ⟨B, hB, hb⟩ := suSphereChart_observedLp_bound g e he
  let T := (B ^ alpha * C) ^ (2 * alpha)⁻¹
  have hap : 0 < 2 * alpha := by linarith
  have hexp : 0 < 1 - 2 / (2 * alpha) := by
    rw [sub_pos, div_lt_one hap]
    linarith
  intro p
  let c := chartAt LoopPlane p
  obtain ⟨K, hK, hmorrey⟩ :=
    Poincare.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_pair_bound_uniform
      (d := 2) (show 2 < 2 * alpha by linarith) (x₀ := c p) (show 0 < (4 : ℝ) by norm_num)
  have hLp (j : ℕ) :
      (eLpNorm (fun z => ‖fderiv ℝ (e ∘ f j ∘ c.symm) z‖)
        (ENNReal.ofReal (2 * alpha)) (volume.restrict (Metric.ball (c p) 4))).toReal ≤ T := by
    obtain ⟨hm, hn, _⟩ := hb alpha ha.le (f j) (hf j) p
    rw [eLpNorm_norm]
    exact (ENNReal.toReal_mono hm.eLpNorm_ne_top
      (eLpNorm_mono_measure _ Measure.restrict_le_self)).trans
      (hn.trans (Real.rpow_le_rpow
        (mul_nonneg (Real.rpow_nonneg hB _) (m60SphereAlphaEnergy_nonneg g alpha _))
        (mul_le_mul_of_nonneg_left (hbound j) (Real.rpow_nonneg hB _))
        (inv_nonneg.mpr hap.le)))
  have hcp : ContinuousAt c p := c.continuousAt (mem_chart_source LoopPlane p)
  have hmod : Tendsto (fun y => K * T * dist (c p) (c y) ^ (1 - 2 / (2 * alpha)))
      (𝓝 p) (𝓝 0) := by
    have hd : Tendsto (fun y => dist (c p) (c y)) (𝓝 p) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := c p)).dist hcp
    have hr := ((Real.continuous_rpow_const hexp.le).continuousAt (x := 0)).tendsto.comp hd
    simpa [Real.zero_rpow hexp.ne'] using hr.const_mul (K * T)
  apply Metric.equicontinuousAt_of_continuity_modulus _ hmod
  have hs : ∀ᶠ y in 𝓝 p, y ∈ c.source := c.open_source.mem_nhds (mem_chart_source LoopPlane p)
  have hy : ∀ᶠ y in 𝓝 p, c y ∈ Metric.ball (c p) 2 :=
    hcp (Metric.ball_mem_nhds (c p) (by norm_num))
  filter_upwards [hs, hy] with y hys hyp j
  have hu : ContDiff ℝ ∞ (e ∘ f j ∘ c.symm) :=
    contMDiff_iff_contDiff.mp (he.comp ((hf j).comp (suSphereChart_smooth p)))
  have hm := hmorrey hu (show c p ∈ Metric.ball (c p) (4 / 2) by simp)
    (show c y ∈ Metric.ball (c p) (4 / 2) by norm_num; exact hyp)
  have ht := mul_le_mul_of_nonneg_left (hLp j)
    (mul_nonneg hK (Real.rpow_nonneg
      (dist_nonneg (x := c p) (y := c y)) (1 - 2 / (2 * alpha))))
  have hh := hm.trans ht
  simpa only [Function.comp_apply, c.left_inv (mem_chart_source LoopPlane p), c.left_inv hys,
    dist_eq_norm, mul_assoc, mul_left_comm, mul_comm] using hh

theorem suAlpha_embedding_equicontinuous
    {n k : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin k))
    (he : ContMDiff (𝓡 n) (𝓡 k) ∞ e) {alpha C : ℝ} (ha : 1 < alpha)
    (f : ℕ → UnitTwoSphere → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hbound : ∀ j, m60SphereAlphaEnergy g alpha (f j) ≤ C) :
    Equicontinuous (fun j => e ∘ f j) := by
  have hpi := (PiLp.uniformEquiv 2 (fun _ : Fin k => ℝ)).isUniformEmbedding.isUniformInducing
  apply hpi.equicontinuous_iff.mpr
  change Equicontinuous (fun j p i => e (f j p) i)
  rw [Pi.uniformSpace_eq, equicontinuous_iInf_rng]
  intro i
  let : UniformSpace (Fin k → ℝ) := UniformSpace.comap (fun v => v i) inferInstance
  have hi : IsUniformInducing (fun v : Fin k → ℝ => v i) := ⟨rfl⟩
  apply hi.equicontinuous_iff.mpr
  exact suAlpha_observed_equicontinuous g (fun x => e x i)
    ((PiLp.proj 2 (fun _ : Fin k => ℝ) i).contDiff.contMDiff.comp he) ha f hf hbound

end M60

end PoincareConjecture
