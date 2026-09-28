import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerStationarity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap LineDeriv

namespace PoincareConjecture.M65Euler




theorem connection_quadratic_bound {N : ℕ}
    {g : RiemannianMetric N (EuclideanSpace ℝ (Fin N))} (D : LeviCivitaData g)
    {K : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ a : EuclideanSpace ℝ (Fin N),
      ‖M65Gauss.connectionCoefficient D y a a‖ ≤ C * ‖a‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := M65Gauss.connectionCoefficient D)
    (M65Gauss.contDiff_connectionCoefficient D).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y hy a
  calc
    _ ≤ ‖M65Gauss.connectionCoefficient D y‖ * ‖a‖ * ‖a‖ :=
      (M65Gauss.connectionCoefficient D y).le_opNorm₂ a a
    _ ≤ max C 0 * ‖a‖ * ‖a‖ := by gcongr; exact (hC y hy).trans (le_max_left _ _)
    _ = _ := by ring




theorem connection_quadratic_integrable {N : ℕ} {μ : Measure LoopPlane}
    {g : RiemannianMetric N (EuclideanSpace ℝ (Fin N))} (D : LeviCivitaData g)
    (X A : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hX : AEStronglyMeasurable X μ) (hA : MemLp A 2 μ)
    {K : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hcap : ∀ᵐ z ∂μ, X z ∈ K) :
    Integrable (fun z => M65Gauss.connectionCoefficient D (X z) (A z) (A z)) μ := by
  have hG := (M65Gauss.contDiff_connectionCoefficient D).continuous
  have hc : Continuous (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) =>
      M65Gauss.connectionCoefficient D p.1 p.2 p.2) :=
    ((hG.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨C, _hC, hbound⟩ := connection_quadratic_bound D hK
  apply ((memLp_two_iff_integrable_sq_norm hA.1).mp hA).const_mul C |>.mono'
    (hc.comp_aestronglyMeasurable (hX.prodMk hA.1))
  filter_upwards [hcap] with z hz
  exact hbound _ hz _

set_option maxHeartbeats 1600000 in






theorem variational_weak_equation {N : ℕ}
    {g : RiemannianMetric N (EuclideanSpace ℝ (Fin N))} (D : LeviCivitaData g)
    (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) (ball x (8 * R)))
    (a : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε)
    (hXcap : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)))
    (hcmp : ∀ (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)), ContDiff ℝ 1 V →
      ∀ CV : NNReal, (∀ y, ‖fderiv ℝ V y‖ ≤ (CV : ℝ)) →
        ∀ (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ ball x R →
          ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
            (∫ z in closedBall x (2 * R), coordinateHalfEnergy g X.value X.derivative z) ≤
              ∫ z in closedBall x (2 * R), coordinateHalfEnergy g
                (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z) :
    ∀ (k : Fin N) (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ ball x R →
      IntegrableOn (fun z => ∑ i : Fin 2,
        (M65Gauss.connectionCoefficient D (X.value z) (X.derivative i z) (X.derivative i z)) k)
        (closedBall x (2 * R)) ∧
      (∫ z in closedBall x (2 * R), ∑ i : Fin 2,
        fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (X.derivative i z) k) =
        ∫ z in closedBall x (2 * R), φ z * ∑ i : Fin 2,
          (M65Gauss.connectionCoefficient D (X.value z)
            (X.derivative i z) (X.derivative i z)) k := by
  intro k φ hc hs
  let K := closedBall x (2 * R)
  let μ := volume.restrict K
  have hK : IsCompact K := isCompact_closedBall _ _
  have hsub : K ⊆ ball x (8 * R) := closedBall_subset_ball (by linarith)
  have hXm := X.value_memLp K hK hsub
  have hAm (i : Fin 2) := X.derivative_memLp i K hK hsub
  have hcap : ∀ᵐ z ∂μ, X.value z ∈ closedBall a (ε / 2) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact ball_subset_closedBall (hXcap (hsub hz))
  let Q := fun z => ∑ i : Fin 2,
    (M65Gauss.connectionCoefficient D (X.value z) (X.derivative i z) (X.derivative i z)) k
  have hQI : Integrable Q μ := by
    apply integrable_finsetSum
    intro i _
    exact (EuclideanSpace.proj (𝕜 := ℝ) k).integrable_comp
      (connection_quadratic_integrable D X.value (X.derivative i) hXm.1 (hAm i)
        (isCompact_closedBall _ _) hcap)
  let L := fun z => ∑ i : Fin 2,
    fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (X.derivative i z) k
  have hLI : Integrable L μ := by
    apply integrable_finsetSum
    intro i _
    exact (((∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} φ).memLp 2 volume).restrict K).integrable_mul
      ((hAm i).eval_piLp k)
  have hφQI : Integrable (fun z => φ z * Q z) μ :=
    IntegrableOn.continuousOn_mul φ.continuous.continuousOn hQI hK
  obtain ⟨V, CV, hV, hCV, hVe⟩ := exists_bounded_metricDual g k a hε
  obtain ⟨_hI, hzero⟩ := integral_firstVariation_eq_zero g x hR X a hε hXcap
    V hV CV hCV φ hc hs (hcmp V hV CV hCV φ hc hs)
  have heq : firstVariationDensity g X.value X.derivative V φ =ᵐ[μ]
      fun z => L z - φ z * Q z := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    have hXε : X.value z ∈ ball a ε :=
      ball_subset_ball (by linarith) (hXcap (hsub hz))
    exact firstVariation_metricDual D X.value X.derivative V φ k z
      (hVe _ hXε).1 (hVe _ hXε).2
  change (∫ z, firstVariationDensity g X.value X.derivative V φ z ∂μ) = 0 at hzero
  rw [integral_congr_ae heq, integral_sub hLI hφQI] at hzero
  exact ⟨hQI, sub_eq_zero.mp hzero⟩

end PoincareConjecture.M65Euler
