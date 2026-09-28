import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M04.ShiEnergyPaths
import Mathlib.Topology.Instances.Matrix










set_option autoImplicit false

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m65Continuous_derivative_column {f : LoopPlane → M}
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (i : Fin 2) :
    Continuous (fun z : LoopPlane =>
      (⟨f z, mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
        TangentBundle (𝓡 n) M)) :=
  (hf.continuous_tangentMap le_rfl).comp
    ((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const))



theorem m65Continuous_areaDensity (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    Continuous (m60AreaDensity g f) := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hgram : Continuous (fun z : LoopPlane => m60AreaGram g f z) :=
    continuous_pi fun i => continuous_pi fun j =>
      (m65Continuous_derivative_column hf i).inner_bundle (m65Continuous_derivative_column hf j)
  exact (continuous_const.max hgram.matrix_det).sqrt



theorem m65Continuous_derivative_column_norm (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (i : Fin 2) :
    Continuous (fun z => g.tangentNorm (f z)
      (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i))) := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact ((m65Continuous_derivative_column hf i).inner_bundle
    (m65Continuous_derivative_column hf i)).sqrt



theorem m65Exists_compact_derivative_bound (g : RiemannianMetric n M)
    {f : LoopPlane → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    {domain : Set LoopPlane} (hcompact : IsCompact domain) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ domain, ∀ v : LoopPlane,
      g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z v) ≤ K * ‖v‖ := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let S : LoopPlane → ℝ := fun z =>
    g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
    g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hS : Continuous S := (m65Continuous_derivative_column_norm g hf 0).add
    (m65Continuous_derivative_column_norm g hf 1)
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz v
  have hsum : S z ≤ max B 0 :=
    (le_abs_self _).trans ((hB z hz).trans (le_max_left _ _))
  have hv : v = v 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      v 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
  let D := mfderiv (𝓡 2) (𝓡 n) f z
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

end PoincareConjecture
