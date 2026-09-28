import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M49.RoundCylinderGram
import PoincareConjecture.Proofs.M49.Mathlib.InverseGramBound
import Mathlib.LinearAlgebra.Matrix.BilinearForm










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Matrix

universe u

namespace PoincareConjecture.M49


set_option backward.isDefEq.respectTransparency false in


theorem roundCylinder_bilinear_error_le_jet (u : ℝ) (hu : u < 1)
    (B : RoundCylinderTwoTensor) (k : ℕ) (z : RoundCylinderSpace)
    (A : LinearMap.BilinForm ℝ (RoundCylinderTangent z))
    (hA : ∀ v w, B z v w = A v w) (v w : RoundCylinderTangent z) :
    |B z v w - EvolvingRoundCylinderMetric u z v w| ≤
      Real.sqrt (roundCylinderJetErrorSquared u B k z) *
        Real.sqrt (EvolvingRoundCylinderMetric u z v v) *
        Real.sqrt (EvolvingRoundCylinderMetric u z w w) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  have hp : p.1 ∈ c.target := c.map_source (mem_chart_source _ _)
  have hcz : c.symm p.1 = z.1 := c.left_inv (mem_chart_source _ _)
  have hz : (c.symm p.1, p.2) = z := Prod.ext hcz rfl
  have hc : c.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(contMDiffOn_chart (I := 𝓡 2) (n := 1)).mdifferentiableOn one_ne_zero,
      (contMDiffOn_chart_symm (I := 𝓡 2) (n := 1)).mdifferentiableOn one_ne_zero⟩
  let D : RoundCylinderCoordinates ≃ₗ[ℝ] RoundCylinderTangent z :=
    (LinearEquiv.ofBijective (mfderiv (𝓡 2) (𝓡 2) c.symm p.1).toLinearMap
      (hc.symm.mfderiv_bijective hp)).prodCongr (LinearEquiv.refl ℝ ℝ)
  let b0 : Module.Basis (Fin 3) ℝ RoundCylinderCoordinates :=
    basisOfLinearIndependentOfCardEqFinrank roundCylinderCoordinateBasis_linearIndependent
      (by simp [RoundCylinderCoordinates, Module.finrank_prod])
  let b := b0.map D
  have hb (i : Fin 3) : b i =
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis i).1,
        (roundCylinderCoordinateBasis i).2) := by
    simp only [b, Module.Basis.map_apply, b0,
      coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  let s : RoundCylinderTangent z →ₗ[ℝ] TangentSpace (𝓡 2) z.1 :=
    ⟨⟨fun v => v.1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  let t : RoundCylinderTangent z →ₗ[ℝ] ℝ :=
    ⟨⟨fun v => v.2, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  let L : RoundCylinderTangent z →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1).toLinearMap.comp s
  let G : LinearMap.BilinForm ℝ (RoundCylinderTangent z) :=
    LinearMap.mk₂ ℝ (fun v w => 2 * (1 - u) * inner ℝ (L v) (L w) + t v * t w)
      (by intros; simp only [map_add, inner_add_left]; ring)
      (by intros; simp only [map_smul, real_inner_smul_left, smul_eq_mul]; ring)
      (by intros; simp only [map_add, inner_add_right]; ring)
      (by intros; simp only [map_smul, real_inner_smul_right, smul_eq_mul]; ring)
  have hGeval (v w : RoundCylinderTangent z) :
      G v w = EvolvingRoundCylinderMetric u z v w := rfl
  have hgram : LinearMap.BilinForm.toMatrix b G = roundCylinderGram u c p := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, hGeval, hb,
      roundCylinderGram, roundCylinderTensorCoefficient]
    rw [hz]
  have hcoeff (i j : Fin 3) : LinearMap.BilinForm.toMatrix b (A - G) i j =
      roundCylinderTensorCoefficient B c p i j - roundCylinderGram u c p i j := by
    rw [LinearMap.BilinForm.toMatrix_apply]
    change A (b i) (b j) - G (b i) (b j) = _
    simp only [hGeval, ← hA, hb, roundCylinderGram, roundCylinderTensorCoefficient]
    rw [hz]
  have hG : (LinearMap.BilinForm.toMatrix b G).PosDef := by
    rw [hgram]
    exact roundCylinderGram_posDef u hu z.1 p hp
  have hbound := Matrix.abs_bilinear_apply_le_inverse_gram_norm hG
    (LinearMap.BilinForm.toMatrix b (A - G)) (b.repr v) (b.repr w)
  rw [← LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec,
    ← LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec,
    ← LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec] at hbound
  simp_rw [hgram, hcoeff] at hbound
  have hbound' : |B z v w - EvolvingRoundCylinderMetric u z v w| ≤
      Real.sqrt (roundCylinderTensorNormSquared u c p
        (roundCylinderIteratedDerivative u c B 0 p)) *
        Real.sqrt (EvolvingRoundCylinderMetric u z v v) *
        Real.sqrt (EvolvingRoundCylinderMetric u z w w) := by
    simpa only [LinearMap.sub_apply, hGeval, hA,
      roundCylinderTensorNormSquared, roundCylinderIteratedDerivative] using hbound
  exact hbound'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (roundCylinder_zeroth_le_jetErrorSquared_of_lt_one u hu B k z))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))


set_option backward.isDefEq.respectTransparency false in


theorem epsilonNeck_bilinear_error_le
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v w : RoundCylinderTangent z) :
    |N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w -
        RoundCylinderMetric z v w| ≤
      N.epsilon * Real.sqrt (RoundCylinderMetric z v v) *
        Real.sqrt (RoundCylinderMetric z w w) := by
  let B : RoundCylinderTwoTensor := fun x a b =>
    N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map x a b
  let A : LinearMap.BilinForm ℝ (RoundCylinderTangent z) :=
    LinearMap.mk₂ ℝ (B z)
      (by intros; simp [B, roundCylinderPullback, map_add, mul_add])
      (by intros; simp [B, roundCylinderPullback, map_smul, smul_eq_mul]; ring)
      (by intros; simp [B, roundCylinderPullback, map_add, mul_add])
      (by intros; simp [B, roundCylinderPullback, map_smul, smul_eq_mul]; ring)
  have hbound := roundCylinder_bilinear_error_le_jet 0 (by norm_num) B
    ⌊N.epsilon⁻¹⌋₊ z A (fun _ _ => rfl) v w
  obtain ⟨bound, hb, hjet⟩ := N.metric_comparison.close.2
  have hsmall : Real.sqrt (roundCylinderJetErrorSquared 0 B ⌊N.epsilon⁻¹⌋₊ z) ≤
      N.epsilon := by
    exact (Real.sqrt_le_iff).2 ⟨N.epsilon_pos.le, (hjet z hz).trans hb.le⟩
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

end PoincareConjecture.M49
