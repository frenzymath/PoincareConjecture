import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerAlphaOne
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerAlphaOneTests
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture.M65Euler

theorem identity_chart_coefficients {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (a : EuclideanSpace ℝ (Fin N)) :
    g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin N)) a).symm =
      g.euclideanCoefficients := by
  funext y
  ext v w
  simp [RiemannianMetric.pullbackCoefficients, RiemannianMetric.euclideanCoefficients]
  rfl

theorem scalar_weak_pairings {N : ℕ} {U : Set LoopPlane}
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) U)
    (i : Fin 2) (a : Fin N) (φ : LoopPlane → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    IntegrableOn (fun z => X.value z a * fderiv ℝ φ z (EuclideanSpace.single i 1)) U ∧
      IntegrableOn (fun z => X.derivative i z a * φ z) U ∧
      (∫ z in U, X.value z a * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        -(∫ z in U, X.derivative i z a * φ z) := by
  let ψ : 𝓢(LoopPlane, ℝ) := hc.toSchwartzMap hφ
  have hV := X.test_value_integrable ψ hc hs i a
  have hD := X.test_derivative_integrable ψ hc hs i a
  have hw := X.weak_derivative ψ hc hs i a
  change IntegrableOn (fun z =>
    fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * X.value z a) U at hV
  change IntegrableOn (fun z => φ z * X.derivative i z a) U at hD
  change (∫ z in U, φ z * X.derivative i z a) =
    -(∫ z in U, fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * X.value z a) at hw
  refine ⟨?_, ?_, ?_⟩
  · simpa only [EuclideanSpace.basisFun_apply, mul_comm] using hV
  · simpa only [mul_comm] using hD
  · simpa only [neg_neg, EuclideanSpace.basisFun_apply, mul_comm] using
      (congrArg Neg.neg hw).symm

theorem variational_chart_smooth {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (hregularity : M65AlphaOneSmoothness g)
    (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) (ball x (8 * R)))
    (hX : ContinuousOn X.value (ball x (8 * R)))
    (a : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε)
    (hXcap : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)))
    (hcmp : ∀ (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)), ContDiff ℝ 1 V →
      ∀ CV : NNReal, (∀ y, ‖fderiv ℝ V y‖ ≤ (CV : ℝ)) →
        ∀ (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ ball x R →
          ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
            (∫ z in closedBall x (2 * R), coordinateHalfEnergy g X.value X.derivative z) ≤
              ∫ z in closedBall x (2 * R), coordinateHalfEnergy g
                (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z) :
    ContDiffAt ℝ ∞ X.value x := by
  have hclosed : closedBall x R ⊆ ball x (8 * R) := closedBall_subset_ball (by linarith)
  have hball := ball_subset_closedBall.trans hclosed
  let Y := restrict_map X hball
  apply hregularity a X.value X.derivative x R hR
  · intro z _
    simp
  · exact hX.mono hclosed
  · exact (X.value_memLp _ (isCompact_closedBall x R) hclosed).mono_measure
      (Measure.restrict_mono_set volume ball_subset_closedBall)
  · intro i
    exact (X.derivative_memLp i _ (isCompact_closedBall x R) hclosed).mono_measure
      (Measure.restrict_mono_set volume ball_subset_closedBall)
  · intro i k φ hφ hc hs
    exact scalar_weak_pairings Y i k φ hφ hc hs
  · simp only [identity_chart_coefficients]
    intro φ hφ hc hs
    exact variational_vector_equation g x hR X a hε hXcap hcmp φ hφ hc hs

theorem minimum_representative_smooth_of_alphaOne {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e) (heinj : Function.Injective e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hregularity : ∀ gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)),
      M65AlphaOneSmoothness gE)
    {U : Set LoopPlane} (hU : IsOpen U) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) (q : LoopPlane → M)
    (hqc : ContinuousOn q U) (hq : q =ᵐ[volume.restrict U] F.value) :
    ContMDiffOn (𝓡 2) (𝓡 3) ∞ q U := by
  intro x hx
  obtain ⟨R, ε, hR, hε, hRU, gE, _DE, X, hX, hsource, hcap, _hmetric,
    _hfields, hcmp⟩ := exists_variational_chart g e he heinj hinj hU F hmin q hqc hq hx
  have hXc : ContinuousOn X.value (ball x (8 * R)) := by
    have hh := (continuousOn_extChartAt (I := 𝓡 3) (q x)).comp
      (hqc.mono (ball_subset_closedBall.trans hRU)) hsource
    exact hh.congr (fun z _ => hX z)
  have hsmooth := variational_chart_smooth gE (hregularity gE) x hR X hXc _ hε hcap hcmp
  have hqinf : ContMDiffAt (𝓡 2) (𝓡 3) ∞ q x := by
    apply contMDiffAt_iff_target.mpr
    refine ⟨hqc.continuousAt (hU.mem_nhds hx), ?_⟩
    apply contMDiffAt_iff_contDiffAt.mpr
    rwa [show X.value = extChartAt (𝓡 3) (q x) ∘ q from funext hX] at hsmooth
  exact hqinf.contMDiffWithinAt

end PoincareConjecture.M65Euler
