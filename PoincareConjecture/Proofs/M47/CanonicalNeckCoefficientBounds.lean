import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderOrdinaryJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistencePullbackSmooth










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)




theorem norm_iteratedFDeriv_weighted_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (lambda mu : ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => lambda * f y - mu * g y) x‖ ≤
      |lambda| * ‖iteratedFDeriv ℝ j (fun y => f y - g y) x‖ +
        |lambda - mu| * ‖iteratedFDeriv ℝ j g x‖ := by
  let L : ℝ →L[ℝ] ℝ := lambda • ContinuousLinearMap.id ℝ ℝ
  let K : ℝ →L[ℝ] ℝ := (lambda - mu) • ContinuousLinearMap.id ℝ ℝ
  have hL : ContDiffAt ℝ ∞ (L ∘ (fun y => f y - g y)) x :=
    L.contDiff.contDiffAt.comp x (hf.sub hg)
  have hK : ContDiffAt ℝ ∞ (K ∘ g) x := K.contDiff.contDiffAt.comp x hg
  have heq : (fun y => lambda * f y - mu * g y) =
      L ∘ (fun y => f y - g y) + K ∘ g := by
    funext y
    change lambda * f y - mu * g y = lambda * (f y - g y) + (lambda - mu) * g y
    ring
  rw [heq, iteratedFDeriv_add_apply
    (hL.of_le (by exact_mod_cast le_top)) (hK.of_le (by exact_mod_cast le_top))]
  apply (norm_add_le _ _).trans
  have hLn : ‖L‖ = |lambda| := by simp [L, norm_smul, Real.norm_eq_abs]
  have hKn : ‖K‖ = |lambda - mu| := by simp [K, norm_smul, Real.norm_eq_abs]
  simpa only [hLn, hKn] using add_le_add
    (L.norm_iteratedFDeriv_comp_left (hf.sub hg) (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞))
    (K.norm_iteratedFDeriv_comp_left hg (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞))




theorem exists_neck_metric_coefficient_jet_bound
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (q : UnitTwoSphere) (z : ℝ),
      z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
            (chartAt E₂ q) y i l) (0, z)‖ ≤ D := by
  obtain ⟨A, _, hA⟩ := capPersistence_exists_coordinate_error_jet_bound m
  obtain ⟨B, _, hB⟩ := capNeckNormalization_exists_modelGram_center_jet_bound 0 m
  let lambda := N.scale⁻¹ ^ 2
  let T : RoundCylinderTwoTensor := fun z v w =>
    lambda * roundCylinderPullback g N.coordinate_map z v w
  let C := A * Real.sqrt (N.epsilon ^ 2 / (1 / 2 : ℝ) ^ (2 + m)) + B
  refine ⟨max 1 (|lambda⁻¹| * C), le_max_left _ _, ?_⟩
  intro q z hz j hj i l
  have hlambda : lambda ≠ 0 := pow_ne_zero _ (inv_ne_zero N.scale_pos.ne')
  have hcenter : (0, z) ∈ (chartAt E₂ q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, hz⟩
    simpa only [sphere_chart_center_zero] using (chartAt E₂ q).map_source (mem_chart_source E₂ q)
  have hT : ContDiffAt ℝ ∞ (fun y =>
      roundCylinderTensorCoefficient T (chartAt E₂ q) y i l) (0, z) :=
    (N.metric_comparison.close.1 q i l).contDiffAt
      (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hcenter)
  have hG : ContDiffAt ℝ ∞ (fun y => roundCylinderGram 0 (chartAt E₂ q) y i l) (0, z) :=
    (capPersistence_modelGram_contDiff 0 q i l).contDiffAt
  have herror := hA N.epsilon T N.metric_comparison.close hm q z hz j hj i l
  have hsub : iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient T (chartAt E₂ q) y i l -
        roundCylinderGram 0 (chartAt E₂ q) y i l) (0, z) =
      iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient T (chartAt E₂ q) y i l) (0, z) -
      iteratedFDeriv ℝ j (fun y => roundCylinderGram 0 (chartAt E₂ q) y i l) (0, z) :=
    iteratedFDeriv_sub_apply (hT.of_le (by exact_mod_cast le_top))
      (hG.of_le (by exact_mod_cast le_top))
  rw [sphere_chart_center_zero, hsub] at herror
  have hnorm : ‖iteratedFDeriv ℝ j (fun y =>
      roundCylinderTensorCoefficient T (chartAt E₂ q) y i l) (0, z)‖ ≤ C :=
    (norm_le_norm_sub_add _ _).trans (add_le_add herror (hB q z j hj i l))
  let L : ℝ →L[ℝ] ℝ := lambda⁻¹ • ContinuousLinearMap.id ℝ ℝ
  have heq : (fun y =>
      roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
        (chartAt E₂ q) y i l) = L ∘ (fun y =>
          roundCylinderTensorCoefficient T (chartAt E₂ q) y i l) := by
    funext y
    change _ = lambda⁻¹ * (lambda * _)
    rw [← mul_assoc, inv_mul_cancel₀ hlambda, one_mul]
    rfl
  rw [heq]
  have hLn : ‖L‖ = |lambda⁻¹| := by simp [L, norm_smul, Real.norm_eq_abs]
  have hjet := L.norm_iteratedFDeriv_comp_left hT (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
  rw [hLn] at hjet
  exact (hjet.trans (mul_le_mul_of_nonneg_left hnorm (abs_nonneg _))).trans (le_max_right _ _)

end PoincareConjecture.Proofs.M47
