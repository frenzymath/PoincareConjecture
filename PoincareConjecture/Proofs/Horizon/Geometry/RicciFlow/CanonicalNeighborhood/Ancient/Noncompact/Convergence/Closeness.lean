import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.EvolvingBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Comparison












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture
namespace TerminalNeck

noncomputable def cylinderDifference (u : ℝ) (B₁ B₀ : RoundCylinderTwoTensor) :
    RoundCylinderTwoTensor := fun z v w =>
  EvolvingRoundCylinderMetric u z v w + B₁ z v w - B₀ z v w

theorem cylinderDifference_coefficient (u : ℝ) (B₁ B₀ : RoundCylinderTwoTensor)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderTensorCoefficient (cylinderDifference u B₁ B₀)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b -
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
    roundCylinderTensorCoefficient B₁ (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b -
      roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b := by
  simp only [roundCylinderGram, cylinderDifference, roundCylinderTensorCoefficient]
  ring

theorem cylinderDifference_iteratedDerivative
    {u : ℝ} (hu : u < 1) (B₁ B₀ : RoundCylinderTwoTensor) (q : UnitTwoSphere)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    (hB₁ : ∀ a b : Fin 3, ContDiffOn ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B₁ (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) U)
    (hB₀ : ∀ a b : Fin 3, ContDiffOn ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) U)
    (k : ℕ) {p : RoundCylinderCoordinates} (hp : p ∈ U) (a : Fin (2 + k) → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (cylinderDifference u B₁ B₀) k p a =
      roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) B₁ k p a -
        roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) B₀ k p a := by
  induction k generalizing p with
  | zero =>
    simp only [roundCylinderIteratedDerivative, cylinderDifference_coefficient]
    ring
  | succ k ih =>
    have heq : (fun y => roundCylinderIteratedDerivative u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (cylinderDifference u B₁ B₀) k y
          (fun i => a i.succ)) =ᶠ[𝓝 p] (fun y =>
        roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
            B₁ k y (fun i => a i.succ) -
          roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
            B₀ k y (fun i => a i.succ)) := by
      filter_upwards [hU.mem_nhds hp] with y hy using ih hy _
    have hs₁ (b : Fin (2 + k) → Fin 3) :=
      contDiffAt_evolvingCylinderIteratedDerivative u hu q
        (fun i j => ((hB₁ i j).contDiffAt (hU.mem_nhds hp)).sub
          (contDiff_roundCylinderGram u q i j).contDiffAt) k b
    have hs₀ (b : Fin (2 + k) → Fin 3) :=
      contDiffAt_evolvingCylinderIteratedDerivative u hu q
        (fun i j => ((hB₀ i j).contDiffAt (hU.mem_nhds hp)).sub
          (contDiff_roundCylinderGram u q i j).contDiffAt) k b
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
    erw [heq.fderiv_eq (𝕜 := ℝ), fderiv_sub ((hs₁ _).differentiableAt (by simp))
      ((hs₀ _).differentiableAt (by simp))]
    simp only [sub_apply, ih hp, mul_sub, Finset.sum_sub_distrib]
    exact sub_sub_sub_comm _ _ _ _

private theorem tensorNorm_weighted_add_le {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) {r : ℕ}
    (X Y : (Fin r → Fin 3) → ℝ) (θ : ℝ) :
    θ * roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (fun a => X a + Y a) ≤
      θ * (1 + θ) * roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p X +
      (1 + θ) * roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p Y := by
  have h := DeepHorn.evolvingCylinderTensorNormSquared_nonneg hu q p
    (fun a => θ * X a - Y a)
  have heq :
      θ * roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
          (fun a => X a + Y a) +
        roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
          (fun a => θ * X a - Y a) =
      θ * (1 + θ) * roundCylinderTensorNormSquared u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p X +
        (1 + θ) * roundCylinderTensorNormSquared u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p Y := by
    simp only [roundCylinderTensorNormSquared, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  linarith

theorem cylinderDifference_jetError_weighted_le
    {u : ℝ} (hu : u < 1) (B₁ B₀ : RoundCylinderTwoTensor)
    {ε : ℝ} (hB₁ : RoundCylinderTensorSmoothOn ε B₁)
    (hB₀ : RoundCylinderTensorSmoothOn ε B₀)
    (m : ℕ) (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    {θ : ℝ} (_hθ : 0 < θ) :
    θ * roundCylinderJetErrorSquared u B₁ m z ≤
      θ * (1 + θ) * roundCylinderJetErrorSquared u B₀ m z +
        (1 + θ) * roundCylinderJetErrorSquared u (cylinderDifference u B₁ B₀) m z := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  have hp : p ∈ c.target ×ˢ Ioo (-ε⁻¹) ε⁻¹ :=
    ⟨c.map_source (mem_chart_source _ _), hz⟩
  have hd (k : ℕ) (a : Fin (2 + k) → Fin 3) :=
    cylinderDifference_iteratedDerivative hu B₁ B₀ z.1 (c.open_target.prod isOpen_Ioo)
      (hB₁ z.1) (hB₀ z.1) k hp a
  unfold roundCylinderJetErrorSquared
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have h := tensorNorm_weighted_add_le hu z.1 p
    (roundCylinderIteratedDerivative u c B₀ k p)
    (roundCylinderIteratedDerivative u c (cylinderDifference u B₁ B₀) k p) θ
  have hadd : (fun a => roundCylinderIteratedDerivative u c B₀ k p a +
      roundCylinderIteratedDerivative u c (cylinderDifference u B₁ B₀) k p a) =
      roundCylinderIteratedDerivative u c B₁ k p := by
    funext a
    have hda := hd k a
    change roundCylinderIteratedDerivative u c (cylinderDifference u B₁ B₀) k p a =
      roundCylinderIteratedDerivative u c B₁ k p a -
        roundCylinderIteratedDerivative u c B₀ k p a at hda
    rw [hda]
    ring
  rw [hadd] at h
  exact h



theorem exists_evolvingCylinder_comparison_tolerance
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (B₀ B₁ : ℝ → RoundCylinderTwoTensor),
      RoundCylinderFamilyClose δ (Ioc (-1 : ℝ) 0) B₀ →
      (∀ u ∈ Ioc (-1 : ℝ) 0, RoundCylinderTensorSmoothOn ε (B₁ u)) →
      (∀ u ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ → ∀ j, j ≤ ⌊ε⁻¹⌋₊ → ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient (B₁ u)
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
              roundCylinderTensorCoefficient (B₀ u)
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η) →
      RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) B₁ := by
  obtain ⟨C, hC, hCb⟩ := exists_evolvingCylinderJetErrorSquared_bound
    (J := Icc (-ε⁻¹) ε⁻¹) isCompact_Icc ⌊ε⁻¹⌋₊
  have hgap : 0 < ε ^ 2 - δ ^ 2 := by nlinarith
  let θ := (ε ^ 2 - δ ^ 2) / (2 * δ ^ 2)
  have hθ : 0 < θ := div_pos hgap (by positivity)
  have hθeq : θ * (2 * δ ^ 2) = ε ^ 2 - δ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  let η := Real.sqrt (θ * (ε ^ 2 - δ ^ 2) / (4 * ((1 + θ) * C + 1)))
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hηsq : η ^ 2 = θ * (ε ^ 2 - δ ^ 2) / (4 * ((1 + θ) * C + 1)) :=
    Real.sq_sqrt (by positivity)
  have hηeq : (4 * ((1 + θ) * C + 1)) * η ^ 2 = θ * (ε ^ 2 - δ ^ 2) := by
    rw [hηsq, mul_div_cancel₀ _ (by positivity)]
  refine ⟨η, hη, ?_⟩
  intro B₀ B₁ hclose hsmooth hjet
  have hs₀ := (DeepHorn.roundCylinderFamilyClose_mono hδ hδε.le
    (fun u hu => by linarith [hu.2]) hclose).1
  refine ⟨hsmooth, (3 * ε ^ 2 + δ ^ 2) / 4, by nlinarith, ?_⟩
  intro u hu z hz
  have hu' : u < 1 := by linarith [hu.2]
  have herr : roundCylinderJetErrorSquared u
      (cylinderDifference u (B₁ u) (B₀ u)) ⌊ε⁻¹⌋₊ z ≤ C * η ^ 2 := by
    apply hCb u ⟨hu.1.le, hu.2⟩ _ z ⟨hz.1.le, hz.2.le⟩ η hη.le
    · intro a b
      simp only [cylinderDifference_coefficient]
      have hp : (0, z.2) ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
          Ioo (-ε⁻¹) ε⁻¹ := by
        rw [roundCylinder_sphereChart_target]
        exact ⟨mem_univ _, hz⟩
      have hn := ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).open_target.prod
        isOpen_Ioo).mem_nhds hp
      exact ((hsmooth u hu z.1 a b).contDiffAt hn).sub
        ((hs₀ u hu z.1 a b).contDiffAt hn)
    · simpa only [cylinderDifference_coefficient] using hjet u hu z hz
  have hlimit : roundCylinderJetErrorSquared u (B₀ u) ⌊ε⁻¹⌋₊ z ≤ δ ^ 2 := by
    obtain ⟨_, bound, hb, hbound⟩ := hclose
    exact (DeepHorn.evolvingCylinderJetErrorSquared_mono hu' (B₀ u) z
      (Nat.floor_mono ((inv_le_inv₀ (hδ.trans hδε) hδ).2 hδε.le))).trans
      ((hbound u hu z (DeepHorn.neckInterval_subset hδ hδε.le hz)).trans hb.le)
  have hweighted := cylinderDifference_jetError_weighted_le hu' (B₁ u) (B₀ u)
    (hsmooth u hu) (hs₀ u hu) ⌊ε⁻¹⌋₊ z hz hθ
  have hbound := hweighted.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlimit (by positivity))
    (mul_le_mul_of_nonneg_left herr (by positivity)))
  apply (mul_le_mul_iff_right₀ hθ).mp
  have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
  nlinarith



theorem eventually_roundCylinderFamilyClose_of_coefficientJets
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    {B₀ : ℝ → RoundCylinderTwoTensor} {B : ℕ → ℝ → RoundCylinderTwoTensor}
    (hclose : RoundCylinderFamilyClose δ (Ioc (-1 : ℝ) 0) B₀)
    (hsmooth : ∀ᶠ k in atTop, ∀ u ∈ Ioc (-1 : ℝ) 0,
      RoundCylinderTensorSmoothOn ε (B k u))
    (hjet : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ u ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ → ∀ j, j ≤ ⌊ε⁻¹⌋₊ → ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient (B k u)
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
              roundCylinderTensorCoefficient (B₀ u)
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η) :
    ∀ᶠ k in atTop, RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) (B k) := by
  obtain ⟨η, hη, hbound⟩ := exists_evolvingCylinder_comparison_tolerance hδ hδε
  filter_upwards [hsmooth, hjet η hη] with k hks hkj
  exact hbound B₀ (B k) hclose hks hkj

end TerminalNeck
end PoincareConjecture
