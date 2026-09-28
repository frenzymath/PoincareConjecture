import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerFirstVariation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerDual











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

namespace PoincareConjecture.M65Euler





theorem integral_firstVariation_eq_zero {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) (ball x (8 * R)))
    (a : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε)
    (hXcap : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)))
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hV : ContDiff ℝ 1 V) (CV : NNReal) (hCV : ∀ y, ‖fderiv ℝ V y‖ ≤ (CV : ℝ))
    (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ ball x R)
    (hcmp : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      (∫ z in closedBall x (2 * R), coordinateHalfEnergy g X.value X.derivative z) ≤
        ∫ z in closedBall x (2 * R), coordinateHalfEnergy g
          (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z) :
    IntegrableOn (firstVariationDensity g X.value X.derivative V φ) (closedBall x (2 * R)) ∧
      (∫ z in closedBall x (2 * R), firstVariationDensity g X.value X.derivative V φ z) = 0 := by
  obtain ⟨hI, hderiv⟩ := variation_energy_hasDerivAt g x hR X a hε hXcap V hV CV hCV φ hc hs
  obtain ⟨δ, hδ, hcmp⟩ := hcmp
  have hzero : variationValue X.value V φ 0 = X.value := by
    funext z
    simp only [variationValue, zero_smul, add_zero]
  have hzeroD : variationField X.value X.derivative V φ 0 = X.derivative := by
    funext i z
    simp only [variationField, zero_smul, add_zero]
  have hmin : IsLocalMin (fun t : ℝ => ∫ z in closedBall x (2 * R), coordinateHalfEnergy g
      (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z) 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have ht' : |t| < δ := by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
    rw [hzero, hzeroD]
    exact hcmp t ht'
  exact ⟨hI, hmin.hasDerivAt_eq_zero hderiv⟩





theorem exists_bounded_metricDual {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N))) (k : Fin N)
    (a : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (C : NNReal),
      ContDiff ℝ 1 V ∧ (∀ y, ‖fderiv ℝ V y‖ ≤ (C : ℝ)) ∧
        ∀ y ∈ ball a ε, V y = metricDualField g k y ∧
          fderiv ℝ V y = fderiv ℝ (metricDualField g k) y := by
  let χ : ContDiffBump a :=
    { rIn := ε
      rOut := 2 * ε
      rIn_pos := hε
      rIn_lt_rOut := by linarith }
  let V := fun y => χ y • metricDualField g k y
  have hV : ContDiff ℝ 1 V :=
    χ.contDiff.smul ((contDiff_metricDualField g k).of_le (by simp))
  have hcomp : HasCompactSupport V := χ.hasCompactSupport.smul_right
  obtain ⟨C, hC⟩ := (hcomp.fderiv ℝ).exists_bound_of_continuous
    (hV.continuous_fderiv one_ne_zero)
  refine ⟨V, ⟨max C 0, le_max_right _ _⟩, hV,
    fun y => (hC y).trans (le_max_left _ _), ?_⟩
  intro y hy
  have heq : V =ᶠ[𝓝 y] metricDualField g k := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hy] with z hz
    change χ z • metricDualField g k z = metricDualField g k z
    simp only [hz, Pi.one_apply, one_smul]
  exact ⟨heq.eq_of_nhds, heq.fderiv_eq⟩





theorem firstVariation_metricDual {N : ℕ}
    {g : RiemannianMetric N (EuclideanSpace ℝ (Fin N))} (D : LeviCivitaData g)
    (X : LoopPlane → EuclideanSpace ℝ (Fin N))
    (A : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (φ : 𝓢(LoopPlane, ℝ)) (k : Fin N) (z : LoopPlane)
    (hV : V (X z) = metricDualField g k (X z))
    (hDV : fderiv ℝ V (X z) = fderiv ℝ (metricDualField g k) (X z)) :
    firstVariationDensity g X A V φ z =
      (∑ i : Fin 2, fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (A i z) k) -
        φ z * ∑ i : Fin 2, (M65Gauss.connectionCoefficient D (X z) (A i z) (A i z)) k := by
  unfold firstVariationDensity
  rw [hV, hDV]
  calc
    _ = ∑ i : Fin 2, (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * (A i z) k -
        φ z * (M65Gauss.connectionCoefficient D (X z) (A i z) (A i z)) k) :=
      Finset.sum_congr rfl fun i _ => metricDual_firstVariation D k (X z) (A i z) _ _
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]

end PoincareConjecture.M65Euler
