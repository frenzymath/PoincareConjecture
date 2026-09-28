import PoincareConjecture.Proofs.M58.Cor18_28_AreaRegularity

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem continuous_disk_derivative_column_norm (g : RiemannianMetric 3 M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) (i : Fin 2) :
    Continuous (fun z => g.tangentNorm (F z)
      (mfderiv (𝓡 2) (𝓡 3) F z (EuclideanSpace.basisFun (Fin 2) ℝ i))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact ((continuous_disk_derivative_column hF i).inner_bundle
    (continuous_disk_derivative_column hF i)).sqrt

theorem exists_disk_derivative_bound (g : RiemannianMetric 3 M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ loopDiskSet, ∀ v : LoopPlane,
      g.tangentNorm (F z) (mfderiv (𝓡 2) (𝓡 3) F z v) ≤ K * ‖v‖ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let S : LoopPlane → ℝ := fun z =>
    g.tangentNorm (F z) (mfderiv (𝓡 2) (𝓡 3) F z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
    g.tangentNorm (F z) (mfderiv (𝓡 2) (𝓡 3) F z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hS : Continuous S := (continuous_disk_derivative_column_norm g hF 0).add
    (continuous_disk_derivative_column_norm g hF 1)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : LoopPlane) 1).exists_bound_of_continuousOn
    hS.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz v
  have hsum : S z ≤ max B 0 :=
    (le_abs_self _).trans ((hB z hz).trans (le_max_left _ _))
  have hv : v = v 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      v 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
  let D := mfderiv (𝓡 2) (𝓡 3) F z
  have hD : D v = v 0 • D (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      v 1 • D (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
    calc
      D v = D (v 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
          v 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1) := congrArg D hv
      _ = _ := by erw [map_add, map_smul, map_smul]
  change ‖D v‖ ≤ max B 0 * ‖v‖
  rw [hD]
  calc
    _ ≤ ‖v 0 • D (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ +
        ‖v 1 • D (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖ := norm_add_le _ _
    _ = ‖v 0‖ * ‖D (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ +
        ‖v 1‖ * ‖D (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖v‖ * (‖D (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ +
        ‖D (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖) := by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v 0) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v 1) (norm_nonneg _))
    _ ≤ ‖v‖ * max B 0 := mul_le_mul_of_nonneg_left hsum (norm_nonneg v)
    _ = max B 0 * ‖v‖ := mul_comm _ _

end PoincareConjecture.Proofs.M58
