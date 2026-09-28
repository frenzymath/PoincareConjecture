import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerComparison
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

namespace PoincareConjecture.M65Euler

def firstVariationDensity {N : ℕ} (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (X : LoopPlane → EuclideanSpace ℝ (Fin N))
    (A : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (φ : 𝓢(LoopPlane, ℝ)) (z : LoopPlane) : ℝ :=
  ∑ i, ((1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients (X z) (φ z • V (X z)) (A i z) (A i z) +
    g.euclideanCoefficients (X z)
      (φ z • fderiv ℝ V (X z) (A i z) +
        fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • V (X z)) (A i z))

private theorem metric_quadratic_integrable {N : ℕ} {μ : Measure LoopPlane}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (X A : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hX : AEStronglyMeasurable X μ) (hA : MemLp A 2 μ)
    {K : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hcap : ∀ᵐ z ∂μ, X z ∈ K) :
    Integrable (fun z => (1 / 2 : ℝ) * g.euclideanCoefficients (X z) (A z) (A z)) μ := by
  have hG : Continuous g.euclideanCoefficients :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous
  have hpair : Continuous (fun p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) =>
      g.euclideanCoefficients p.1 p.2 p.2) :=
    ((hG.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := g.euclideanCoefficients) hG.continuousOn
  have hAsq := (memLp_two_iff_integrable_sq_norm hA.1).mp hA
  apply (hAsq.const_mul ((1 / 2 : ℝ) * max C 0)).mono'
    ((hpair.comp_aestronglyMeasurable (hX.prodMk hA.1)).const_mul (1 / 2 : ℝ))
  filter_upwards [hcap] with z hz
  have hb := (g.euclideanCoefficients (X z)).le_opNorm₂ (A z) (A z)
  have hCz : ‖g.euclideanCoefficients (X z)‖ ≤ max C 0 := (hC _ hz).trans (le_max_left _ _)
  calc
    _ = (1 / 2 : ℝ) * ‖g.euclideanCoefficients (X z) (A z) (A z)‖ := by simp [norm_mul]
    _ ≤ (1 / 2 : ℝ) * (max C 0 * ‖A z‖ * ‖A z‖) :=
      mul_le_mul_of_nonneg_left (hb.trans (by gcongr)) (by norm_num)
    _ = _ := by ring

set_option maxHeartbeats 2400000 in

theorem variation_energy_hasDerivAt {N : ℕ}
    (g : RiemannianMetric N (EuclideanSpace ℝ (Fin N)))
    (x : LoopPlane) {R : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) (ball x (8 * R)))
    (a : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε)
    (hXcap : MapsTo X.value (ball x (8 * R)) (ball a (ε / 2)))
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hV : ContDiff ℝ 1 V) (CV : NNReal) (hCV : ∀ y, ‖fderiv ℝ V y‖ ≤ (CV : ℝ))
    (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ ball x R) :
    IntegrableOn (firstVariationDensity g X.value X.derivative V φ) (closedBall x (2 * R)) ∧
      HasDerivAt (fun t : ℝ => ∫ z in closedBall x (2 * R), coordinateHalfEnergy g
        (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z)
        (∫ z in closedBall x (2 * R), firstVariationDensity g X.value X.derivative V φ z) 0 := by
  let K := closedBall x (2 * R)
  let μ := volume.restrict K
  let W := fun z => φ z • V (X.value z)
  let B := fun (i : Fin 2) z => φ z • fderiv ℝ V (X.value z) (X.derivative i z) +
    fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • V (X.value z)
  have h28 : K ⊆ ball x (8 * R) := closedBall_subset_ball (by linarith)
  have h26 : K ⊆ ball x (6 * R) := closedBall_subset_ball (by linarith)
  have h68 : closedBall x (6 * R) ⊆ ball x (8 * R) := closedBall_subset_ball (by linarith)
  have hφ6 := hs.trans (ball_subset_ball (by linarith : R ≤ 6 * R))
  let Z1 := weak_variation_on_ball X isOpen_ball x (show 0 ≤ 6 * R by positivity)
    h68 V hV CV hCV φ hc hφ6 1
  have hXm := X.value_memLp K (isCompact_closedBall _ _) h28
  have hAm (i : Fin 2) := X.derivative_memLp i K (isCompact_closedBall _ _) h28
  have hWm : MemLp W 2 μ := by
    apply ((Z1.value_memLp K (isCompact_closedBall _ _) h26).sub hXm).ae_eq
    exact ae_of_all _ fun z => by
      change X.value z + (1 : ℝ) • W z - X.value z = W z
      simp only [one_smul, add_sub_cancel_left]
  have hBm (i : Fin 2) : MemLp (B i) 2 μ := by
    apply ((Z1.derivative_memLp i K (isCompact_closedBall _ _) h26).sub (hAm i)).ae_eq
    exact ae_of_all _ fun z => by
      change X.derivative i z + (1 : ℝ) • B i z - X.derivative i z = B i z
      simp only [one_smul, add_sub_cancel_left]
  obtain ⟨Cφ, hCφ⟩ := hc.exists_bound_of_continuous φ.continuous
  obtain ⟨CV0, hCV0⟩ := (isCompact_closedBall a (ε / 2)).exists_bound_of_continuousOn
    hV.continuous.continuousOn
  let L := max Cφ 0 * max CV0 0
  have hL : 0 ≤ L := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hWbound : ∀ᵐ z ∂μ, ‖W z‖ ≤ L := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    rw [show W z = φ z • V (X.value z) from rfl, norm_smul]
    exact mul_le_mul ((hCφ z).trans (le_max_left _ _))
      ((hCV0 _ (ball_subset_closedBall (hXcap (h28 hz)))).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  obtain ⟨δ, hδ, hcap⟩ := exists_variation_capture X.value V hV.continuous φ hc a hε hXcap
  have hcapture : ∀ᵐ z ∂μ, ∀ t : ℝ, |t| < δ → X.value z + t • W z ∈ closedBall a ε := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz t ht
    exact ball_subset_closedBall (hcap t ht (h28 hz))
  let P := fun i z => (1 / 2 : ℝ) * fderiv ℝ g.euclideanCoefficients (X.value z) (W z)
      (X.derivative i z) (X.derivative i z) +
    g.euclideanCoefficients (X.value z) (B i z) (X.derivative i z)
  let E := fun (i : Fin 2) (t : ℝ) z => (1 / 2 : ℝ) *
    g.euclideanCoefficients (X.value z + t • W z)
      (X.derivative i z + t • B i z) (X.derivative i z + t • B i z)
  have hi (i : Fin 2) : Integrable (P i) μ ∧
      HasDerivAt (fun t : ℝ => ∫ z, E i t z ∂μ) (∫ z, P i z ∂μ) 0 :=
    hasDerivAt_integral_quadratic g X.value W (X.derivative i) (B i) hXm.1 hWm.1
      (hAm i) (hBm i) hL hδ hWbound (closedBall a ε) (isCompact_closedBall a ε) hcapture
  have hEi (i : Fin 2) (t : ℝ) (ht : |t| < δ) : Integrable (E i t) μ :=
    metric_quadratic_integrable g _ _ (hXm.1.add (hWm.1.const_smul t))
      ((hAm i).add ((hBm i).const_smul t)) (isCompact_closedBall a ε)
      (hcapture.mono (fun _ hz => hz t ht))
  have hsumI : Integrable (fun z => ∑ i, P i z) μ :=
    integrable_finsetSum _ fun i _ => (hi i).1
  have hsumD := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hi i).2)
  have hderivEq : (∑ i, ∫ z, P i z ∂μ) =
      ∫ z, firstVariationDensity g X.value X.derivative V φ z ∂μ := by
    exact (integral_finsetSum _ fun i _ => (hi i).1).symm
  have heq : (fun t : ℝ => ∫ z, coordinateHalfEnergy g
      (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z ∂μ)
      =ᶠ[𝓝 0] fun t => ∑ i, ∫ z, E i t z ∂μ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have ht' : |t| < δ := by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
    have hpoint : (fun z => coordinateHalfEnergy g
        (variationValue X.value V φ t) (variationField X.value X.derivative V φ t) z) =
        fun z => ∑ i, E i t z := by
      funext z
      change (1 / 2 : ℝ) * (∑ i, g.euclideanCoefficients (X.value z + t • W z)
        (X.derivative i z + t • B i z) (X.derivative i z + t • B i z)) = _
      exact Finset.mul_sum _ _ _
    rw [hpoint, integral_finsetSum _ fun i _ => hEi i t ht']
  exact ⟨hsumI, (hsumD.congr_deriv hderivEq).congr_of_eventuallyEq heq⟩

end PoincareConjecture.M65Euler
