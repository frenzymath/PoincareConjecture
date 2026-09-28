import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ModelComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Closeness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SingularRegularLimit

theorem cylinder_scaled_static_jetError_short_tail
    {ε c d s : ℝ} (hε : 0 < ε) (hc : 1 ≤ c) (hcmax : c ≤ 6 / 5)
    (hcε : c - 1 ≤ ε / 4) (hdε : d ≤ ε / 4)
    (hs : -d ≤ s) (hszero : s ≤ 0)
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose ε 0 B)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-(2 * ε)⁻¹) (2 * ε)⁻¹) :
    roundCylinderJetErrorSquared s (fun z v w => c * B z v w) ⌊(2 * ε)⁻¹⌋₊ z ≤
      (7 / 2 : ℝ) * ε ^ 2 := by
  have hweak : ε ≤ 2 * ε := by linarith
  have hz' := DeepHorn.neckInterval_subset hε hweak hz
  have horder : ⌊(2 * ε)⁻¹⌋₊ ≤ ⌊ε⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ (by positivity) hε).2 hweak)
  have hold : roundCylinderJetErrorSquared 0 B ⌊(2 * ε)⁻¹⌋₊ z ≤ ε ^ 2 :=
    (DeepHorn.evolvingCylinderJetErrorSquared_mono (by norm_num) B z horder).trans
      ((hB.2.choose_spec.2 z hz').trans hB.2.choose_spec.1.le)
  have hestimate := cylinder_scaled_jetError_le_explicit hszero (by norm_num)
    hB.1 c ⌊(2 * ε)⁻¹⌋₊ z hz'
  have hden : 0 < 1 - s := by linarith
  have hnumabs : |c * (1 - (0 : ℝ)) - (1 - s)| ≤ ε / 4 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hratio : |(c * (1 - (0 : ℝ)) - (1 - s)) / (1 - s)| ≤ ε / 4 := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hratio2 : ((c * (1 - (0 : ℝ)) - (1 - s)) / (1 - s)) ^ 2 ≤ (ε / 4) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ ε / 4 by positivity)).2 hratio
  have hc2 : c ^ 2 ≤ (36 / 25 : ℝ) := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ε)
  have hsmall : (c - 1) ^ 2 ≤ (ε / 4) ^ 2 := by nlinarith
  have hold' := mul_le_mul_of_nonneg_left hold (show 0 ≤ 2 * c ^ 2 by positivity)
  nlinarith

theorem exists_short_tail_coefficient_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {c d : ℝ},
      1 ≤ c → c ≤ 6 / 5 → c - 1 ≤ ε / 4 → d ≤ ε / 4 →
      ∀ (B₀ : RoundCylinderTwoTensor) (B : ℝ → RoundCylinderTwoTensor),
        RoundCylinderClose ε 0 B₀ →
        (∀ s ∈ Ioc (-1 : ℝ) 0 ∩ Ici (-d), RoundCylinderTensorSmoothOn (2 * ε) (B s)) →
        (∀ s ∈ Ioc (-1 : ℝ) 0 ∩ Ici (-d), ∀ z : RoundCylinderSpace,
          z.2 ∈ Ioo (-(2 * ε)⁻¹) (2 * ε)⁻¹ → ∀ j ≤ ⌊(2 * ε)⁻¹⌋₊, ∀ a b : Fin 3,
            ‖iteratedFDeriv ℝ j (fun y =>
              roundCylinderTensorCoefficient (B s)
                  (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
                roundCylinderTensorCoefficient (fun z v w => c * B₀ z v w)
                  (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η) →
        RoundCylinderFamilyClose (2 * ε) (Ioc (-1 : ℝ) 0 ∩ Ici (-d)) B := by
  obtain ⟨C, hC, hbound⟩ := TerminalNeck.exists_evolvingCylinderJetErrorSquared_bound
    (J := Icc (-(2 * ε)⁻¹) (2 * ε)⁻¹) isCompact_Icc ⌊(2 * ε)⁻¹⌋₊
  let η := Real.sqrt (ε ^ 2 / (100 * (C + 1)))
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hηsq : η ^ 2 = ε ^ 2 / (100 * (C + 1)) := Real.sq_sqrt (by positivity)
  have hηeq : (100 * (C + 1)) * η ^ 2 = ε ^ 2 := by
    rw [hηsq, mul_div_cancel₀ _ (by positivity)]
  have hCη : C * η ^ 2 ≤ ε ^ 2 / 100 := by nlinarith [sq_nonneg η]
  refine ⟨η, hη, ?_⟩
  intro c d hc hcmax hcε hdε B₀ B hclose hsmooth hjet
  let Bscaled : RoundCylinderTwoTensor := fun z v w => c * B₀ z v w
  have hscaled : RoundCylinderTensorSmoothOn (2 * ε) Bscaled := by
    intro q a b
    exact (contDiffOn_const.mul (hclose.1 q a b)).mono
      (prod_mono subset_rfl (DeepHorn.neckInterval_subset hε (by linarith)))
  refine ⟨hsmooth, (39 / 10 : ℝ) * ε ^ 2, by nlinarith [sq_pos_of_pos hε], ?_⟩
  intro s hs z hz
  have hsone : s < 1 := by linarith [hs.1.2]
  have herr : roundCylinderJetErrorSquared s
      (TerminalNeck.cylinderDifference s (B s) Bscaled) ⌊(2 * ε)⁻¹⌋₊ z ≤ C * η ^ 2 := by
    apply hbound s ⟨hs.1.1.le, hs.1.2⟩ _ z ⟨hz.1.le, hz.2.le⟩ η hη.le
    · intro a b
      simp only [TerminalNeck.cylinderDifference_coefficient]
      have hp : (0, z.2) ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
          Ioo (-(2 * ε)⁻¹) (2 * ε)⁻¹ := by
        rw [roundCylinder_sphereChart_target]
        exact ⟨mem_univ _, hz⟩
      have hn := ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).open_target.prod
        isOpen_Ioo).mem_nhds hp
      exact ((hsmooth s hs z.1 a b).contDiffAt hn).sub ((hscaled z.1 a b).contDiffAt hn)
    · simpa only [TerminalNeck.cylinderDifference_coefficient] using hjet s hs z hz
  have hold := cylinder_scaled_static_jetError_short_tail hε hc hcmax hcε hdε
    hs.2 hs.1.2 hclose z hz
  have hweighted := TerminalNeck.cylinderDifference_jetError_weighted_le hsone
    (B s) Bscaled (hsmooth s hs) hscaled ⌊(2 * ε)⁻¹⌋₊ z hz
    (show (0 : ℝ) < 1 / 20 by norm_num)
  nlinarith

end PoincareConjecture.SingularRegularLimit
