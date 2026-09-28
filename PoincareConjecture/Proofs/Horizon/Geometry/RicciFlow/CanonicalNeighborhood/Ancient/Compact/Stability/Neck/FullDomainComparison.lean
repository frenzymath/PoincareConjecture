import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderCoefficientField










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.TerminalNeck



theorem exists_fullDomainCylinder_coefficient_tolerance
    {ε : ℝ} (hε : 0 < ε) {B₀ : RoundCylinderTwoTensor}
    (hclose : RoundCylinderClose ε 0 B₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ B₁ : RoundCylinderTwoTensor,
      RoundCylinderTensorSmoothOn ε B₁ →
      (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
        ∀ j, j ≤ ⌊ε⁻¹⌋₊ → ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient B₁
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
              roundCylinderTensorCoefficient B₀
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η) →
      RoundCylinderClose ε 0 B₁ := by
  obtain ⟨hs₀, bound, hbound, hlimit⟩ := hclose
  let b := max bound 0
  have hb : 0 ≤ b := le_max_right _ _
  have hbε : b < ε ^ 2 := max_lt hbound (sq_pos_of_pos hε)
  obtain ⟨C, hC, hCb⟩ := exists_evolvingCylinderJetErrorSquared_bound
    (J := Icc (-ε⁻¹) ε⁻¹) isCompact_Icc ⌊ε⁻¹⌋₊
  let θ := (ε ^ 2 - b) / (2 * (b + 1))
  have hθ : 0 < θ := div_pos (sub_pos.mpr hbε) (by positivity)
  have hθeq : θ * (2 * (b + 1)) = ε ^ 2 - b :=
    div_mul_cancel₀ _ (by positivity)
  have hθb : θ * b ≤ (ε ^ 2 - b) / 2 := by nlinarith
  have hθb' := mul_le_mul_of_nonneg_left hθb hθ.le
  let η := Real.sqrt (θ * (ε ^ 2 - b) / (4 * ((1 + θ) * C + 1)))
  have hη : 0 < η := Real.sqrt_pos.2 (div_pos (mul_pos hθ (sub_pos.mpr hbε)) (by positivity))
  have hηsq : η ^ 2 = θ * (ε ^ 2 - b) / (4 * ((1 + θ) * C + 1)) :=
    Real.sq_sqrt (by positivity)
  have hηeq : (4 * ((1 + θ) * C + 1)) * η ^ 2 = θ * (ε ^ 2 - b) := by
    rw [hηsq, mul_div_cancel₀ _ (by positivity)]
  refine ⟨η, hη, ?_⟩
  intro B₁ hs₁ hjet
  refine ⟨hs₁, (3 * ε ^ 2 + b) / 4, by linarith, ?_⟩
  intro z hz
  have herr : roundCylinderJetErrorSquared 0 (cylinderDifference 0 B₁ B₀)
      ⌊ε⁻¹⌋₊ z ≤ C * η ^ 2 := by
    apply hCb 0 (by constructor <;> norm_num) _ z ⟨hz.1.le, hz.2.le⟩ η hη.le
    · intro a c
      simp only [cylinderDifference_coefficient]
      have hp : (0, z.2) ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
          Ioo (-ε⁻¹) ε⁻¹ := by
        rw [roundCylinder_sphereChart_target]
        exact ⟨mem_univ _, hz⟩
      have hn := ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).open_target.prod
        isOpen_Ioo).mem_nhds hp
      exact ((hs₁ z.1 a c).contDiffAt hn).sub ((hs₀ z.1 a c).contDiffAt hn)
    · simpa only [cylinderDifference_coefficient] using hjet z hz
  have hlim : roundCylinderJetErrorSquared 0 B₀ ⌊ε⁻¹⌋₊ z ≤ b :=
    (hlimit z hz).trans (le_max_left _ _)
  have hweighted := cylinderDifference_jetError_weighted_le (by norm_num : (0 : ℝ) < 1)
    B₁ B₀ hs₁ hs₀ ⌊ε⁻¹⌋₊ z hz hθ
  have hsum := hweighted.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlim (by positivity))
    (mul_le_mul_of_nonneg_left herr (by positivity)))
  apply (mul_le_mul_iff_right₀ hθ).mp
  have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
  nlinarith

open MetricSurgery

private theorem centered_error_contDiffAt_of_tensorSmooth
    {ε : ℝ} {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn ε B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    ContDiffAt ℝ ∞ (centeredCylinderError B z.1 z.2) 0 := by
  apply centeredCylinderBilinear_contDiffAt
  intro a b
  have hp : (0, z.2) ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
      Ioo (-ε⁻¹) ε⁻¹ := by
    rw [roundCylinder_sphereChart_target]
    exact ⟨mem_univ _, hz⟩
  have hn := ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).open_target.prod
    isOpen_Ioo).mem_nhds hp
  exact ((hB z.1 a b).contDiffAt hn).sub (contDiff_roundCylinderGram 0 z.1 a b).contDiffAt



theorem norm_coefficientJet_le_centeredDifferenceJet
    {ε : ℝ} {B₀ B₁ : RoundCylinderTwoTensor}
    (hB₀ : RoundCylinderTensorSmoothOn ε B₀) (hB₁ : RoundCylinderTensorSmoothOn ε B₁)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (j : ℕ) (a b : Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B₁ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
          roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b)
      (0, z.2)‖ ≤
      ‖iteratedFDeriv ℝ j (fun p => centeredCylinderError B₁ z.1 z.2 p -
        centeredCylinderError B₀ z.1 z.2 p) 0‖ *
          ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ ^ j := by
  let F := fun p => centeredCylinderError B₁ z.1 z.2 p - centeredCylinderError B₀ z.1 z.2 p
  let basis := EuclideanSpace.basisFun (Fin 3) ℝ
  let f := fun y =>
    roundCylinderTensorCoefficient B₁ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
      roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b
  let coeff := fun p => F p (basis a) (basis b)
  have hF : ContDiffAt ℝ ∞ F 0 :=
    (centered_error_contDiffAt_of_tensorSmooth hB₁ z hz).sub
      (centered_error_contDiffAt_of_tensorSmooth hB₀ z hz)
  have hnorm : ‖iteratedFDeriv ℝ j coeff 0‖ ≤ ‖iteratedFDeriv ℝ j F 0‖ := by
    have h₁ := norm_iteratedFDeriv_clm_apply_const hF
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top) (c := basis a)
    have h₂ := norm_iteratedFDeriv_clm_apply_const
      (hF.clm_apply (contDiffAt_const (c := basis a)))
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top) (c := basis b)
    simp only [basis.norm_eq_one, one_mul] at h₁ h₂
    exact h₂.trans h₁
  have heq : (fun y => f (y + (0, z.2))) = coeff ∘ cylinderEuclideanEquiv.symm := by
    funext y
    simp only [coeff, F, basis, Function.comp_apply, sub_apply,
      centeredCylinderError, centeredCylinderBilinear_basis,
      ContinuousLinearEquiv.apply_symm_apply]
    dsimp only [f]
    ring
  have hj : iteratedFDeriv ℝ j f (0, z.2) =
      (iteratedFDeriv ℝ j coeff 0).compContinuousLinearMap
        (fun _ => cylinderEuclideanEquiv.symm.toContinuousLinearMap) := by
    calc
      _ = iteratedFDeriv ℝ j (fun y => f (y + (0, z.2))) 0 := by
        rw [iteratedFDeriv_comp_add_right, zero_add]
      _ = _ := by
        rw [heq]
        simpa only [preimage_univ, iteratedFDerivWithin_univ, map_zero] using
          cylinderEuclideanEquiv.symm.iteratedFDerivWithin_comp_right coeff
            uniqueDiffOn_univ (x := 0) (mem_univ _) j
  change ‖iteratedFDeriv ℝ j f (0, z.2)‖ ≤ _
  rw [hj]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    mul_le_mul_of_nonneg_right hnorm (pow_nonneg (norm_nonneg _) j)



theorem exists_fullDomainCylinder_comparison_tolerance
    {ε : ℝ} (hε : 0 < ε) {B₀ : RoundCylinderTwoTensor}
    (hclose : RoundCylinderClose ε 0 B₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ B₁ : RoundCylinderTwoTensor,
      RoundCylinderTensorSmoothOn ε B₁ →
      (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
        ∀ j, j ≤ ⌊ε⁻¹⌋₊ →
          ‖iteratedFDeriv ℝ j (fun p => centeredCylinderError B₁ z.1 z.2 p -
            centeredCylinderError B₀ z.1 z.2 p) 0‖ ≤ η) →
      RoundCylinderClose ε 0 B₁ := by
  obtain ⟨η₀, hη₀, htolerance⟩ := exists_fullDomainCylinder_coefficient_tolerance hε hclose
  let C := max ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ 1
  have hC : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let η := η₀ / C ^ ⌊ε⁻¹⌋₊
  have hη : 0 < η := div_pos hη₀ (pow_pos hCpos _)
  refine ⟨η, hη, ?_⟩
  intro B₁ hs₁ hjet
  apply htolerance B₁ hs₁
  intro z hz j hj a b
  have hpower : ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ ^ j ≤
      C ^ ⌊ε⁻¹⌋₊ :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) j).trans
      (pow_le_pow_right₀ hC hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun p => centeredCylinderError B₁ z.1 z.2 p -
          centeredCylinderError B₀ z.1 z.2 p) 0‖ *
            ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ ^ j :=
      norm_coefficientJet_le_centeredDifferenceJet hclose.1 hs₁ z hz j a b
    _ ≤ η * C ^ ⌊ε⁻¹⌋₊ := mul_le_mul (hjet z hz j hj) hpower
      (pow_nonneg (norm_nonneg _) _) hη.le
    _ = η₀ := div_mul_cancel₀ _ (ne_of_gt (pow_pos hCpos _))



theorem eventually_roundCylinderClose_of_centeredDifferenceJets
    {ι : Type*} {l : Filter ι} {ε : ℝ} (hε : 0 < ε)
    {B₀ : RoundCylinderTwoTensor} {B : ι → RoundCylinderTwoTensor}
    (hclose : RoundCylinderClose ε 0 B₀)
    (hsmooth : ∀ᶠ k in l, RoundCylinderTensorSmoothOn ε (B k))
    (hjet : ∀ η : ℝ, 0 < η → ∀ᶠ k in l,
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
        ∀ j, j ≤ ⌊ε⁻¹⌋₊ →
          ‖iteratedFDeriv ℝ j (fun p => centeredCylinderError (B k) z.1 z.2 p -
            centeredCylinderError B₀ z.1 z.2 p) 0‖ ≤ η) :
    ∀ᶠ k in l, RoundCylinderClose ε 0 (B k) := by
  obtain ⟨η, hη, htolerance⟩ := exists_fullDomainCylinder_comparison_tolerance hε hclose
  filter_upwards [hsmooth, hjet η hη] with k hsk hjk
  exact htolerance (B k) hsk hjk

end PoincareConjecture.TerminalNeck
