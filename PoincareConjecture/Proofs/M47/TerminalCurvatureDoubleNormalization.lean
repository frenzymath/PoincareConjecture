import PoincareConjecture.Proofs.M47.TerminalCurvatureDoubleMargin
import PoincareConjecture.Proofs.M47.TerminalCurvatureUniformCoefficients
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCovariantDifference










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open M34 PoincareConjecture.Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)



theorem terminalCurvature_exists_double_normalization_tolerance
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 / 2 ∧
      ∀ D : RoundCylinderTwoTensor, RoundCylinderClose epsilon 0 D →
      ∀ B : RoundCylinderTwoTensor, RoundCylinderTensorSmoothOn (2 * epsilon) B →
      (∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ →
        ∀ j ≤ Nat.floor (2 * epsilon)⁻¹, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
              roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) (0, z)‖ ≤ rho) →
      ∀ beta : ℝ, |beta - 1| ≤ sigma →
        RoundCylinderClose (2 * epsilon) 0 (fun z v w => beta * B z v w) := by
  obtain ⟨eta, heta, hperturb⟩ := terminalCurvature_exists_double_neck_array_tolerance hepsilon
  obtain ⟨L, hL, hLbound⟩ := terminalCurvature_exists_uniform_neck_coefficient_bound epsilon
  let K : Set RoundCylinderCoordinates :=
    ({0} : Set E₂) ×ˢ Icc (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹
  obtain ⟨A, hA, hAbound⟩ := exists_roundCylinder_covariant_difference_component_bound
    (isCompact_singleton (x := (0 : ℝ)))
    (by rintro u rfl; norm_num : ({0} : Set ℝ) ⊆ Iio 1)
    (isCompact_singleton.prod isCompact_Icc : IsCompact K) (Nat.floor (2 * epsilon)⁻¹)
  let delta := eta / (A + 1)
  have hdelta : 0 < delta := div_pos heta (by positivity)
  have hsmall : A * delta ≤ eta := by
    have heq : (A + 1) * delta = eta := by dsimp only [delta]; field_simp
    nlinarith
  let rho := delta / 4
  let sigma := min (1 / 2 : ℝ) (delta / (4 * (L + 1)))
  have hrho : 0 < rho := div_pos hdelta (by norm_num)
  have hden : 0 < 4 * (L + 1) := by linarith
  have hsigma : 0 < sigma := lt_min (by norm_num) (div_pos hdelta hden)
  have hsigmaHalf : sigma ≤ 1 / 2 := min_le_left _ _
  have htotal : 2 * rho + sigma * L ≤ delta := by
    have h := (le_div_iff₀ hden).mp
      (min_le_right (1 / 2 : ℝ) (delta / (4 * (L + 1))))
    change sigma * (4 * (L + 1)) ≤ delta at h
    dsimp only [rho]
    nlinarith
  have hinv : (2 * epsilon)⁻¹ ≤ epsilon⁻¹ := inv_anti₀ hepsilon (by linarith)
  have horder := Nat.floor_mono hinv
  have hdomain : Ioo (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ ⊆
      Ioo (-epsilon⁻¹) epsilon⁻¹ := fun _ hz =>
    ⟨(neg_le_neg hinv).trans_lt hz.1, hz.2.trans_le hinv⟩
  refine ⟨rho, hrho, sigma, hsigma, hsigmaHalf, ?_⟩
  intro D hD B hB hjet beta hbeta
  have hDs : RoundCylinderTensorSmoothOn (2 * epsilon) D :=
    hD.1.mono_epsilon hepsilon (by linarith)
  have hbetaBound : |beta| ≤ 2 := by
    have h := abs_le.mp (hbeta.trans hsigmaHalf)
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  let T : RoundCylinderTwoTensor := fun z v w => beta * B z v w
  have hT : RoundCylinderTensorSmoothOn (2 * epsilon) T := hB.const_mul
  apply hperturb D hD T hT
  intro z hz k hk a
  have hcenter : (0, z.2) ∈ (chartAt E₂ z.1).target ×ˢ
      Ioo (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ z.1).map_source (mem_chart_source E₂ z.1)
  have h := hAbound 0 (mem_singleton 0) z.1 T D (2 * epsilon) hT hDs (0, z.2)
    ⟨mem_singleton 0, hz.1.le, hz.2.le⟩ hcenter delta hdelta.le
    (fun j hj i l => ?_) k hk a
  · simpa only [sphere_chart_center_zero] using h.trans hsmall
  · have hnew := (hB z.1 i l).contDiffAt
      (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds hcenter)
    have hold := (hDs z.1 i l).contDiffAt
      (((chartAt E₂ z.1).open_target.prod isOpen_Ioo).mem_nhds hcenter)
    have hw := norm_iteratedFDeriv_weighted_sub_le hnew hold beta 1 j
    simp only [one_mul] at hw
    apply hw.trans
    exact (add_le_add
      (mul_le_mul hbetaBound (hjet z.1 z.2 hz j hj i l) (norm_nonneg _) (by norm_num))
      (mul_le_mul hbeta (hLbound D hD z.1 z.2 (hdomain hz) j (hj.trans horder) i l)
        (norm_nonneg _) hsigma.le)).trans htotal

end PoincareConjecture.M47
