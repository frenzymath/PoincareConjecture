import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.TerminalNeck

theorem exists_fullDomainCylinderFamily_coefficient_tolerance
    {ε : ℝ} (hε : 0 < ε) {B₀ : ℝ → RoundCylinderTwoTensor}
    (hclose : RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) B₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ B₁ : ℝ → RoundCylinderTwoTensor,
      (∀ u ∈ Ioc (-1 : ℝ) 0, RoundCylinderTensorSmoothOn ε (B₁ u)) →
      (∀ u ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ → ∀ j, j ≤ ⌊ε⁻¹⌋₊ → ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient (B₁ u)
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
              roundCylinderTensorCoefficient (B₀ u)
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η) →
      RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) B₁ := by
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
  have hη : 0 < η :=
    Real.sqrt_pos.2 (div_pos (mul_pos hθ (sub_pos.mpr hbε)) (by positivity))
  have hηsq : η ^ 2 = θ * (ε ^ 2 - b) / (4 * ((1 + θ) * C + 1)) :=
    Real.sq_sqrt (by positivity)
  have hηeq : (4 * ((1 + θ) * C + 1)) * η ^ 2 = θ * (ε ^ 2 - b) := by
    rw [hηsq, mul_div_cancel₀ _ (by positivity)]
  refine ⟨η, hη, ?_⟩
  intro B₁ hs₁ hjet
  refine ⟨hs₁, (3 * ε ^ 2 + b) / 4, by linarith, ?_⟩
  intro u hu z hz
  have hu' : u < 1 := by linarith [hu.2]
  have herr : roundCylinderJetErrorSquared u (cylinderDifference u (B₁ u) (B₀ u))
      ⌊ε⁻¹⌋₊ z ≤ C * η ^ 2 := by
    apply hCb u ⟨hu.1.le, hu.2⟩ _ z ⟨hz.1.le, hz.2.le⟩ η hη.le
    · intro a c
      simp only [cylinderDifference_coefficient]
      have hp : (0, z.2) ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
          Ioo (-ε⁻¹) ε⁻¹ := by
        rw [roundCylinder_sphereChart_target]
        exact ⟨mem_univ _, hz⟩
      have hn := ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).open_target.prod
        isOpen_Ioo).mem_nhds hp
      exact ((hs₁ u hu z.1 a c).contDiffAt hn).sub
        ((hs₀ u hu z.1 a c).contDiffAt hn)
    · simpa only [cylinderDifference_coefficient] using hjet u hu z hz
  have hlim : roundCylinderJetErrorSquared u (B₀ u) ⌊ε⁻¹⌋₊ z ≤ b :=
    (hlimit u hu z hz).trans (le_max_left _ _)
  have hweighted := cylinderDifference_jetError_weighted_le hu' (B₁ u) (B₀ u)
    (hs₁ u hu) (hs₀ u hu) ⌊ε⁻¹⌋₊ z hz hθ
  have hsum := hweighted.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlim (by positivity))
    (mul_le_mul_of_nonneg_left herr (by positivity)))
  apply (mul_le_mul_iff_right₀ hθ).mp
  have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
  nlinarith

open MetricSurgery

theorem exists_fullDomainCylinderFamily_comparison_tolerance
    {ε : ℝ} (hε : 0 < ε) {B₀ : ℝ → RoundCylinderTwoTensor}
    (hclose : RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) B₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ B₁ : ℝ → RoundCylinderTwoTensor,
      (∀ u ∈ Ioc (-1 : ℝ) 0, RoundCylinderTensorSmoothOn ε (B₁ u)) →
      (∀ u ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ → ∀ j, j ≤ ⌊ε⁻¹⌋₊ →
          ‖iteratedFDeriv ℝ j (fun p => centeredCylinderError (B₁ u) z.1 z.2 p -
            centeredCylinderError (B₀ u) z.1 z.2 p) 0‖ ≤ η) →
      RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) B₁ := by
  obtain ⟨η₀, hη₀, htolerance⟩ :=
    exists_fullDomainCylinderFamily_coefficient_tolerance hε hclose
  let C := max ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ 1
  have hC : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let η := η₀ / C ^ ⌊ε⁻¹⌋₊
  have hη : 0 < η := div_pos hη₀ (pow_pos hCpos _)
  refine ⟨η, hη, ?_⟩
  intro B₁ hs₁ hjet
  apply htolerance B₁ hs₁
  intro u hu z hz j hj a b
  have hpower : ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ ^ j ≤
      C ^ ⌊ε⁻¹⌋₊ :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) j).trans
      (pow_le_pow_right₀ hC hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun p => centeredCylinderError (B₁ u) z.1 z.2 p -
          centeredCylinderError (B₀ u) z.1 z.2 p) 0‖ *
            ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ ^ j :=
      norm_coefficientJet_le_centeredDifferenceJet (hclose.1 u hu) (hs₁ u hu) z hz j a b
    _ ≤ η * C ^ ⌊ε⁻¹⌋₊ := mul_le_mul (hjet u hu z hz j hj) hpower
      (pow_nonneg (norm_nonneg _) _) hη.le
    _ = η₀ := div_mul_cancel₀ _ (ne_of_gt (pow_pos hCpos _))

theorem eventually_roundCylinderFamilyClose_of_centeredDifferenceJets_fullDomain
    {ι : Type*} {l : Filter ι} {ε : ℝ} (hε : 0 < ε)
    {B₀ : ℝ → RoundCylinderTwoTensor} {B : ι → ℝ → RoundCylinderTwoTensor}
    (hclose : RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) B₀)
    (hsmooth : ∀ᶠ k in l, ∀ u ∈ Ioc (-1 : ℝ) 0,
      RoundCylinderTensorSmoothOn ε (B k u))
    (hjet : ∀ η : ℝ, 0 < η → ∀ᶠ k in l,
      ∀ u ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ → ∀ j, j ≤ ⌊ε⁻¹⌋₊ →
          ‖iteratedFDeriv ℝ j (fun p => centeredCylinderError (B k u) z.1 z.2 p -
            centeredCylinderError (B₀ u) z.1 z.2 p) 0‖ ≤ η) :
    ∀ᶠ k in l, RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) (B k) := by
  obtain ⟨η, hη, htolerance⟩ := exists_fullDomainCylinderFamily_comparison_tolerance hε hclose
  filter_upwards [hsmooth, hjet η hη] with k hsk hjk
  exact htolerance (B k) hsk hjk

end PoincareConjecture.TerminalNeck
