import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityDecay
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import PoincareConjecture.Proofs.M60.Mathlib.ConformalPlaneLaplacian
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.Analysis.SpecialFunctions.SmoothTransition










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def suLogPolar (x : LoopPlane) : LoopPlane :=
  Real.exp (-x 0) • Proofs.M58.angularPoint (x 1)

theorem suLogPolar_contDiff : ContDiff ℝ ∞ suLogPolar := by
  have h0 : ContDiff ℝ ∞ (fun x : LoopPlane => x 0) := by fun_prop
  have h1 : ContDiff ℝ ∞ (fun x : LoopPlane => x 1) := by fun_prop
  exact h0.neg.exp.smul (Proofs.M58.contDiff_angularPoint.comp h1)

theorem suLogPolar_norm (x : LoopPlane) : ‖suLogPolar x‖ = Real.exp (-x 0) := by
  rw [suLogPolar, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Proofs.M58.norm_angularPoint, mul_one]

theorem suLogPolar_fderiv (x v : LoopPlane) :
    fderiv ℝ suLogPolar x v = (-v 0 * Real.exp (-x 0)) • Proofs.M58.angularPoint (x 1) +
      (v 1 * Real.exp (-x 0)) • Proofs.M58.angularVector (x 1) := by
  have h0 : HasFDerivAt (𝕜 := ℝ) (fun y : LoopPlane => y 0)
      (EuclideanSpace.proj (0 : Fin 2)) x :=
    (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 0).hasFDerivAt
  have h1 : HasFDerivAt (𝕜 := ℝ) (fun y : LoopPlane => y 1)
      (EuclideanSpace.proj (1 : Fin 2)) x :=
    (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 1).hasFDerivAt
  have hexp : HasFDerivAt (𝕜 := ℝ) (fun y : LoopPlane => Real.exp (-y 0)) _ x :=
    h0.neg.exp
  have hang := (Proofs.M58.hasDerivAt_angularPoint (x 1)).hasFDerivAt.comp x h1
  have hh := hexp.smul hang
  change HasFDerivAt suLogPolar _ x at hh
  rw [hh.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, EuclideanSpace.coe_proj, Function.comp_def, Pi.neg_apply, smul_smul]
  module

theorem suLogPolar_gram (x : LoopPlane) (i j : Fin 2) :
    inner ℝ (fderiv ℝ suLogPolar x (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (fderiv ℝ suLogPolar x (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
      Real.exp (-x 0) ^ 2 * (if i = j then 1 else 0) := by
  rw [suLogPolar_fderiv, suLogPolar_fderiv]
  simp only [PiLp.inner_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [EuclideanSpace.basisFun_apply, Proofs.M58.angularPoint, Proofs.M58.angularVector,
      mul_pow, sq_abs] <;>
    nlinarith [congrArg (fun r : ℝ => Real.exp (-x 0) ^ 2 * r)
      (Real.sin_sq_add_cos_sq (x 1))]

theorem suLogPolar_det (x : LoopPlane) :
    (fderiv ℝ suLogPolar x).det = -(Real.exp (-x 0) ^ 2) := by
  change LinearMap.det (fderiv ℝ suLogPolar x).toLinearMap = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    ContinuousLinearMap.coe_coe]
  change (fderiv ℝ suLogPolar x (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 0 *
      (fderiv ℝ suLogPolar x (EuclideanSpace.basisFun (Fin 2) ℝ 1)) 1 -
    (fderiv ℝ suLogPolar x (EuclideanSpace.basisFun (Fin 2) ℝ 1)) 0 *
      (fderiv ℝ suLogPolar x (EuclideanSpace.basisFun (Fin 2) ℝ 0)) 1 = _
  simp only [suLogPolar_fderiv]
  simp [EuclideanSpace.basisFun_apply, Proofs.M58.angularPoint, Proofs.M58.angularVector]
  nlinarith [congrArg (fun r : ℝ => Real.exp (-x 0) ^ 2 * r)
    (Real.sin_sq_add_cos_sq (x 1))]

theorem suLogPolar_laplacian (x : LoopPlane) :
    fderiv ℝ (fderiv ℝ suLogPolar) x (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (fderiv ℝ suLogPolar) x (EuclideanSpace.basisFun (Fin 2) ℝ 1)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0 := by
  have hbij : Function.Bijective (fderiv ℝ suLogPolar x) := by
    apply (Module.End.isUnit_iff _).mp
    apply (LinearMap.isUnit_iff_isUnit_det _).mpr
    rw [isUnit_iff_ne_zero]
    change (fderiv ℝ suLogPolar x).det ≠ 0
    rw [suLogPolar_det]
    exact neg_ne_zero.mpr (pow_ne_zero 2 (Real.exp_ne_zero _))
  apply laplacian_eq_zero_of_conformal_plane (suLogPolar_contDiff.contDiffAt.of_le
    (WithTop.coe_le_coe.mpr le_top))
    hbij.surjective
  · exact Eventually.of_forall (fun y => by dsimp only; rw [suLogPolar_gram, suLogPolar_gram]; rfl)
  · exact Eventually.of_forall (fun y => by dsimp only; rw [suLogPolar_gram]; simp)

theorem suLogPolar_energy (g : RiemannianMetric n M) (φ : LoopPlane → M) (x : LoopPlane)
    (hφ : MDifferentiableAt (𝓡 2) (𝓡 n) φ (suLogPolar x)) :
    m60EnergyDensity g (φ ∘ suLogPolar) x =
      Real.exp (-x 0) ^ 2 * m60EnergyDensity g φ (suLogPolar x) := by
  let A := mfderiv (𝓡 2) (𝓡 n) φ (suLogPolar x)
  let B : LinearMap.BilinForm ℝ LoopPlane :=
    (g.inner (φ (suLogPolar x))).toBilinForm.compl₁₂ A.toLinearMap A.toLinearMap
  have hh := sum_bilinear_conformal_basis B (EuclideanSpace.basisFun (Fin 2) ℝ)
    (fun i => fderiv ℝ suLogPolar x (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (by simp) (sq_pos_of_pos (Real.exp_pos _)) (suLogPolar_gram x)
  simp only [m60EnergyDensity, Matrix.trace_fin_two, m60AreaGram]
  rw [mfderiv_comp x hφ (suLogPolar_contDiff.contMDiff.mdifferentiable (by simp) x),
    mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_def]
  simp only [B, A, ContinuousLinearMap.toBilinForm_apply,
    LinearMap.compl₁₂_apply, Fin.sum_univ_two, ContinuousLinearMap.coe_coe] at hh
  erw [hh]
  ring_nf
  rfl

private def punctureClock (t : ℝ) : ℝ :=
  1 + (t + 1) * Real.smoothTransition (t + 1)

private theorem punctureClock_pos (t : ℝ) : 0 < punctureClock t := by
  unfold punctureClock
  by_cases ht : 0 ≤ t + 1
  · have hs := Real.smoothTransition.nonneg (t + 1)
    positivity
  · rw [Real.smoothTransition.zero_of_nonpos (le_of_not_ge ht), mul_zero, add_zero]
    exact zero_lt_one

private theorem punctureClock_eq (t : ℝ) (ht : 0 ≤ t) : punctureClock t = t + 2 := by
  unfold punctureClock
  rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  ring

def punctureCoordinates (x : LoopPlane) : LoopPlane :=
  suLogPolar (suCylinderPoint (punctureClock (x 0)) (x 1))

private theorem punctureCoordinates_contDiff : ContDiff ℝ ∞ punctureCoordinates := by
  apply suLogPolar_contDiff.comp
  unfold suCylinderPoint punctureClock
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  fun_prop

private theorem punctureCoordinates_range (x : LoopPlane) :
    punctureCoordinates x ∈ Metric.ball (0 : LoopPlane) 1 \ {0} := by
  have hn : ‖punctureCoordinates x‖ = Real.exp (-punctureClock (x 0)) := by
    rw [punctureCoordinates, suLogPolar_norm, cylinderPoint_zero]
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, hn, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (punctureClock_pos _)
  · intro hx
    rw [mem_singleton_iff] at hx
    rw [hx, norm_zero] at hn
    exact (Real.exp_pos _).ne' hn.symm

private theorem logPolar_integrable {q : LoopPlane → ℝ}
    (hq : IntegrableOn q (Metric.ball (0 : LoopPlane) 1 \ {0})) :
    IntegrableOn (fun x : LoopPlane => Real.exp (-x 0) ^ 2 * q (suLogPolar x))
      {x | 0 < x 0 ∧ x 1 ∈ Ioo (-Real.pi) Real.pi} := by
  let S : Set LoopPlane := {x | 0 < x 0 ∧ x 1 ∈ Ioo (-Real.pi) Real.pi}
  have hS : MeasurableSet S := by
    have hc (i : Fin 2) : Continuous (fun x : LoopPlane => x i) := by fun_prop
    exact ((isOpen_lt continuous_const (hc 0)).inter
      ((hc 1).isOpen_preimage _ isOpen_Ioo)).measurableSet
  have hp (x : LoopPlane) : suLogPolar x = Proofs.M58.loopPlaneEquivProd.symm
      (polarCoord.symm (Real.exp (-x 0), x 1)) := by
    exact (Proofs.M58.loopPlaneEquivProd_symm_polar (Real.exp (-x 0), x 1)).symm
  have hi : InjOn suLogPolar S := by
    intro x hx y hy hxy
    rw [hp, hp] at hxy
    have hpol := Proofs.M58.loopPlaneEquivProd.symm.injective hxy
    have hx' : (Real.exp (-x 0), x 1) ∈ polarCoord.target := ⟨Real.exp_pos _, hx.2⟩
    have hy' : (Real.exp (-y 0), y 1) ∈ polarCoord.target := ⟨Real.exp_pos _, hy.2⟩
    have he := polarCoord.symm.injOn hx' hy' hpol
    have h0 := neg_injective (Real.exp_injective (congrArg Prod.fst he))
    have h1 := congrArg Prod.snd he
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hr : suLogPolar '' S ⊆ Metric.ball (0 : LoopPlane) 1 \ {0} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, suLogPolar_norm, Real.exp_lt_one_iff]
      exact neg_neg_of_pos hx.1
    · intro hz
      have hh := suLogPolar_norm x
      rw [mem_singleton_iff] at hz
      rw [hz, norm_zero] at hh
      exact (Real.exp_pos _).ne' hh.symm
  have hh := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS
    (fun x _ => ((suLogPolar_contDiff.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt)
    hi q).mp (hq.mono_set hr)
  simp only [suLogPolar_det, abs_neg, abs_pow, Real.abs_exp, smul_eq_mul] at hh
  exact hh

omit [IsManifold (𝓡 n) ∞ M] in
theorem punctureMap_smooth {φ : LoopPlane → M}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ (Metric.ball (0 : LoopPlane) 1 \ {0})) :
    ContMDiff (𝓡 2) (𝓡 n) ∞ (φ ∘ punctureCoordinates) := by
  intro x
  exact (hφ.contMDiffAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds
    (punctureCoordinates_range x))).comp x (punctureCoordinates_contDiff.contMDiff x)

private theorem punctureCoordinates_eventually {x : LoopPlane} (hx : 0 < x 0) :
    punctureCoordinates =ᶠ[𝓝 x]
      (fun y => suLogPolar (2 • EuclideanSpace.basisFun (Fin 2) ℝ 0 + y)) := by
  have hc : Continuous (fun y : LoopPlane => y 0) := by fun_prop
  filter_upwards [hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)] with y hy
  unfold punctureCoordinates
  congr 1
  rw [punctureClock_eq _ hy.le]
  ext i
  fin_cases i
  · simp [suCylinderPoint, EuclideanSpace.basisFun_apply]
    ring
  · simp [suCylinderPoint, EuclideanSpace.basisFun_apply]

theorem punctureCoordinates_periodic (x : LoopPlane) :
    punctureCoordinates (x + (2 * Real.pi) • EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      punctureCoordinates x := by
  have hs (t θ : ℝ) : suCylinderPoint t θ 1 = θ := by
    simp [suCylinderPoint, EuclideanSpace.basisFun_apply]
  have h0 : (x + (2 * Real.pi) • EuclideanSpace.basisFun (Fin 2) ℝ 1) 0 = x 0 := by
    simp [EuclideanSpace.basisFun_apply]
  have h1 : (x + (2 * Real.pi) • EuclideanSpace.basisFun (Fin 2) ℝ 1) 1 = x 1 + 2 * Real.pi := by
    simp [EuclideanSpace.basisFun_apply]
  simp only [punctureCoordinates, suLogPolar, cylinderPoint_zero, hs, h0, h1]
  have hp : Proofs.M58.angularPoint (x 1 + 2 * Real.pi) = Proofs.M58.angularPoint (x 1) := by
    ext i
    fin_cases i <;> simp [Proofs.M58.angularPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]
  rw [hp]

private theorem energy_translate_at (g : RiemannianMetric n M)
    {φ : LoopPlane → M} (a x : LoopPlane)
    (hφ : MDifferentiableAt (𝓡 2) (𝓡 n) φ (a + x)) :
    m60EnergyDensity g (fun y => φ (a + y)) x = m60EnergyDensity g φ (a + x) := by
  have hs : HasMFDerivAt (𝓡 2) (𝓡 2) (fun y : LoopPlane => a + y) x
      (ContinuousLinearMap.id ℝ LoopPlane) :=
    ((hasFDerivAt_id x).const_add a).hasMFDerivAt
  have hd := mfderiv_comp x hφ hs.mdifferentiableAt
  rw [hs.mfderiv] at hd
  unfold m60EnergyDensity m60AreaGram
  change (1 / 2 : ℝ) * Matrix.trace (fun i j => g.inner _
    (mfderiv (𝓡 2) (𝓡 n) (φ ∘ (fun y => a + y)) x _)
    (mfderiv (𝓡 2) (𝓡 n) (φ ∘ (fun y => a + y)) x _)) = _
  rw [hd]
  rfl

theorem punctureMap_energy (g : RiemannianMetric n M) {φ : LoopPlane → M}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ (Metric.ball (0 : LoopPlane) 1 \ {0}))
    {x : LoopPlane} (hx : 0 < x 0) :
    m60EnergyDensity g (φ ∘ punctureCoordinates) x =
      Real.exp (-(x 0 + 2)) ^ 2 * m60EnergyDensity g φ (punctureCoordinates x) := by
  let a := 2 • EuclideanSpace.basisFun (Fin 2) ℝ 0
  have he := punctureCoordinates_eventually hx
  have he0 : punctureCoordinates x = suLogPolar (a + x) := he.eq_of_nhds
  have hat : MDifferentiableAt (𝓡 2) (𝓡 n) φ (suLogPolar (a + x)) := by
    rw [← he0]
    exact (hφ.contMDiffAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds
      (punctureCoordinates_range x))).mdifferentiableAt (by simp)
  have heφ : (φ ∘ punctureCoordinates) =ᶠ[𝓝 x] (fun y => (φ ∘ suLogPolar) (a + y)) :=
    he.mono (fun y hy => congrArg φ hy)
  rw [m60EnergyDensity_congr_of_eventuallyEq g heφ,
    energy_translate_at g a x (hat.comp (a + x)
      (suLogPolar_contDiff.contMDiff.mdifferentiable (by simp) (a + x))),
    suLogPolar_energy g φ (a + x) hat, ← he0]
  have ha : (a + x) 0 = x 0 + 2 := by
    simp [a, EuclideanSpace.basisFun_apply, add_comm]
  rw [ha]

theorem punctureMap_harmonic (g : RiemannianMetric n M) {φ : LoopPlane → M}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ (Metric.ball (0 : LoopPlane) 1 \ {0}))
    (hharm : ∀ b : M, ∀ z ∈ Metric.ball (0 : LoopPlane) 1 \ {0},
      φ z ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0)
    (b : M) (x : LoopPlane) (hx : 0 < x 0)
    (hb : φ (punctureCoordinates x) ∈ (extChartAt (𝓡 n) b).source) :
    let U := extChartAt (𝓡 n) b ∘ (φ ∘ punctureCoordinates)
    let Γ := CoordinateExponential.christoffelBilinear
      (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
    ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ U
      (fun y => fderiv ℝ U y (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0 := by
  let a := 2 • EuclideanSpace.basisFun (Fin 2) ℝ 0
  let u := extChartAt (𝓡 n) b ∘ φ
  let U := extChartAt (𝓡 n) b ∘ (φ ∘ punctureCoordinates)
  let w := u ∘ suLogPolar
  let Γ := CoordinateExponential.christoffelBilinear
    (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
  have he := punctureCoordinates_eventually hx
  have he0 : punctureCoordinates x = suLogPolar (a + x) := he.eq_of_nhds
  have hr : suLogPolar (a + x) ∈ Metric.ball (0 : LoopPlane) 1 \ {0} :=
    he0 ▸ punctureCoordinates_range x
  have hbu : φ (suLogPolar (a + x)) ∈ (extChartAt (𝓡 n) b).source := he0 ▸ hb
  have hφat := hφ.contMDiffAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hr)
  have hu : ContDiffAt ℝ 2 u (suLogPolar (a + x)) :=
    (contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' (x := b) (n := ∞)
      (by simpa only [extChartAt_source] using hbu)).comp _ hφat)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hU : ContDiffAt ℝ 2 U x :=
    (contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' (x := b) (n := ∞)
      (by simpa only [extChartAt_source, Function.comp_def] using hb)).comp x
        (punctureMap_smooth hφ x))).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hτ := hharm b (suLogPolar (a + x)) hr hbu
  change (∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
    (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (suLogPolar (a + x))) = 0 at hτ
  simp only [Fin.sum_univ_two, ConnectionVariation.covDerivAlong, fderiv_column hu] at hτ
  have hw := covariant_laplacian_comp_eq_zero Γ hu
    (suLogPolar_contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    (sq_pos_of_pos (Real.exp_pos (-(a + x) 0))) (suLogPolar_gram (a + x))
    (suLogPolar_laplacian (a + x)) (by convert hτ using 1; abel)
  have heU : U =ᶠ[𝓝 x] (fun y => w (a + y)) :=
    he.mono (fun y hy => congrArg u hy)
  have hder : fderiv ℝ U x = fderiv ℝ w (a + x) :=
    heU.fderiv_eq.trans (fderiv_comp_add_left a)
  have hder2 : fderiv ℝ (fderiv ℝ U) x = fderiv ℝ (fderiv ℝ w) (a + x) := by
    rw [heU.fderiv.fderiv_eq]
    have hf : fderiv ℝ (fun y => w (a + y)) = fun y => fderiv ℝ w (a + y) :=
      funext (fun _ => fderiv_comp_add_left a)
    rw [hf]
    exact fderiv_comp_add_left a
  change (∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ U
    (fun y => fderiv ℝ U y (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (EuclideanSpace.basisFun (Fin 2) ℝ i) x) = 0
  simp only [Fin.sum_univ_two, ConnectionVariation.covDerivAlong, fderiv_column hU,
    hder2, hder, heU.eq_of_nhds]
  convert hw using 1; abel

theorem punctureMap_finite_energy (g : RiemannianMetric n M) {φ : LoopPlane → M}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ (Metric.ball (0 : LoopPlane) 1 \ {0}))
    (hfinite : IntegrableOn (m60EnergyDensity g φ) (Metric.ball (0 : LoopPlane) 1 \ {0})) :
    IntegrableOn (fun t => ∫ θ in 0..(2 * Real.pi),
      m60EnergyDensity g (φ ∘ punctureCoordinates) (suCylinderPoint t θ)) (Ioi 0) := by
  let a := 2 • EuclideanSpace.basisFun (Fin 2) ℝ 0
  let S : Set LoopPlane := {x | 0 < x 0 ∧ x 1 ∈ Ioo (-Real.pi) Real.pi}
  let R := fun x : LoopPlane => Real.exp (-x 0) ^ 2 * m60EnergyDensity g φ (suLogPolar x)
  let Q := m60EnergyDensity g (φ ∘ punctureCoordinates)
  have hS : MeasurableSet S := by
    have hc (i : Fin 2) : Continuous (fun x : LoopPlane => x i) := by fun_prop
    exact ((isOpen_lt continuous_const (hc 0)).inter
      ((hc 1).isOpen_preimage _ isOpen_Ioo)).measurableSet
  have ha0 (x : LoopPlane) : (a + x) 0 = x 0 + 2 := by
    simp [a, EuclideanSpace.basisFun_apply, add_comm]
  have ha1 (x : LoopPlane) : (a + x) 1 = x 1 := by
    simp [a, EuclideanSpace.basisFun_apply]
  have hshift : (fun x => a + x) '' S ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    change 0 < (a + x) 0 ∧ (a + x) 1 ∈ Ioo (-Real.pi) Real.pi
    rw [ha0, ha1]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hiR : IntegrableOn (fun x => R (a + x)) S :=
    ((measurePreserving_add_left volume a).integrableOn_image (measurableEmbedding_addLeft a)).mp
      ((logPolar_integrable hfinite).mono_set hshift)
  have hiQ : IntegrableOn Q S := hiR.congr (by
    filter_upwards [ae_restrict_mem hS] with x hx
    have he := (punctureCoordinates_eventually hx.1).eq_of_nhds
    dsimp only [Q]
    rw [punctureMap_energy g hφ hx.1]
    simp only [R, ha0, he, a])
  have hp (p : ℝ × ℝ) : Proofs.M58.loopPlaneEquivProd.symm p = suCylinderPoint p.1 p.2 := by
    ext i
    fin_cases i <;> simp [Proofs.M58.loopPlaneEquivProd, suCylinderPoint,
      EuclideanSpace.basisFun_apply]
  have hpre : Proofs.M58.loopPlaneEquivProd.symm ⁻¹' S =
      Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    rfl
  have hip := (Proofs.M58.measurePreserving_loopPlaneEquivProd.symm.integrableOn_comp_preimage
    Proofs.M58.loopPlaneEquivProd.symm.measurableEmbedding).mpr hiQ
  rw [hpre] at hip
  change Integrable (Q ∘ Proofs.M58.loopPlaneEquivProd.symm)
    ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)) at hip
  rw [← Measure.prod_restrict] at hip
  have hi := hip.integral_prod_left
  simp only [Function.comp_def, hp] at hi
  have hψ := punctureMap_smooth hφ
  have hper (x : LoopPlane) :
      Q (x + (2 * Real.pi) • EuclideanSpace.basisFun (Fin 2) ℝ 1) = Q x := by
    let b := (2 * Real.pi) • EuclideanSpace.basisFun (Fin 2) ℝ 1
    have he : (fun y => (φ ∘ punctureCoordinates) (b + y)) = φ ∘ punctureCoordinates := by
      funext y
      dsimp only [Function.comp_def, b]
      rw [add_comm, punctureCoordinates_periodic]
    have hh := energy_translate_at g b x ((hψ (b + x)).mdifferentiableAt (by simp))
    rw [he] at hh
    simpa only [Q, b, add_comm] using hh.symm
  have hcircle (t : ℝ) : (∫ θ in Ioo (-Real.pi) Real.pi, Q (suCylinderPoint t θ)) =
      ∫ θ in 0..(2 * Real.pi), Q (suCylinderPoint t θ) := by
    have hper' : Function.Periodic (fun θ => Q (suCylinderPoint t θ)) (2 * Real.pi) := by
      intro θ
      have he : suCylinderPoint t (θ + 2 * Real.pi) =
          suCylinderPoint t θ + (2 * Real.pi) • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
        simp only [suCylinderPoint, add_smul]
        abel
      dsimp only
      rw [he, hper]
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
    simpa only [he, zero_add] using hper'.intervalIntegral_add_eq (-Real.pi) 0
  simp_rw [hcircle] at hi
  exact hi

theorem punctureCoordinates_inverse {z : LoopPlane} (hz : z ≠ 0)
    (hsmall : ‖z‖ ≤ Real.exp (-2)) :
    ∃ θ ∈ Icc 0 (2 * Real.pi),
      punctureCoordinates (suCylinderPoint (-Real.log ‖z‖ - 2) θ) = z := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hzn.le), inv_mul_cancel₀ hzn.ne']
  obtain ⟨θ, hθ, he⟩ := Proofs.M58.exists_angularPoint ⟨(‖z‖⁻¹ : ℝ) • z, hn⟩
  refine ⟨θ, hθ, ?_⟩
  have ht : 0 ≤ -Real.log ‖z‖ - 2 := by
    have hh := (Real.log_le_iff_le_exp hzn).mpr hsmall
    linarith only [hh]
  have hs (t : ℝ) : suCylinderPoint t θ 1 = θ := by
    simp [suCylinderPoint, EuclideanSpace.basisFun_apply]
  simp only [punctureCoordinates, suLogPolar, cylinderPoint_zero, hs, punctureClock_eq _ ht]
  rw [show -(-Real.log ‖z‖ - 2 + 2) = Real.log ‖z‖ by ring, Real.exp_log hzn, he]
  simp only [smul_smul, mul_inv_cancel₀ hzn.ne', one_smul]

end PoincareConjecture.M60

