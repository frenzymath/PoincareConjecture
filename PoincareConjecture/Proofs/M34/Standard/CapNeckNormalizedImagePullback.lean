import PoincareConjecture.Proofs.M34.Standard.CapNeckImageIdentities
import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalization
import PoincareConjecture.Proofs.M34.Standard.CapIsometryPullback










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)




theorem shifted_image_pullback_eq (h : RiemannianMetric 3 X)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hsource : N.carrier ⊆ e.source) (c : ℝ) (z : RoundCylinderSpace)
    (hz : z.2 + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback h (fun z => e (N.coordinate_map (z.1, z.2 + c))) z v w =
      roundCylinderPullback h (e ∘ N.coordinate_map) (M34.cylinderAxialTranslation c z) v w := by
  let y : RoundCylinderSpace := M34.cylinderAxialTranslation c z
  have hNy : N.coordinate_map y ∈ e.source := hsource (N.coordinate_map_mem_of_axial_mem hz)
  have hN : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map y :=
    N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)
  have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e (N.coordinate_map y) :=
    hf.contMDiffAt (e.open_source.mem_nhds hNy)
  have hd : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (e ∘ N.coordinate_map) y := (he.comp y hN).mdifferentiableAt (by simp)
  have ht := (M34.cylinderAxialTranslation_contMDiff c).mdifferentiable (by simp) z
  have hchain := mfderiv_comp z hd ht
  change h.inner _ (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      ((e ∘ N.coordinate_map) ∘ M34.cylinderAxialTranslation c) z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        ((e ∘ N.coordinate_map) ∘ M34.cylinderAxialTranslation c) z w) = _
  rw [hchain]
  simp only [ContinuousLinearMap.comp_apply, M34.cylinderAxialTranslation_mfderiv]
  rfl




theorem normalized_shifted_image_tensor_eq (h : RiemannianMetric 3 X)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hsource : N.carrier ⊆ e.source) {R : ℝ} (hR : 0 < R)
    (c : ℝ) (z : RoundCylinderSpace)
    (hz : z.2 + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    (R ^ (-1 / 2 : ℝ))⁻¹ ^ 2 *
      roundCylinderPullback h (fun z => e (N.coordinate_map (z.1, z.2 + c))) z v w =
      (N.scale ^ 2 * R) * M34.roundCylinderShift c
        (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback h (e ∘ N.coordinate_map) z v w)
        z v w := by
  have hr : (R ^ (-1 / 2 : ℝ))⁻¹ ^ 2 = R := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hR.le, inv_inv,
      ← Real.sqrt_eq_rpow, Real.sq_sqrt hR.le]
  rw [hr, N.shifted_image_pullback_eq h e hf hsource c z hz v w]
  change R * _ = (N.scale ^ 2 * R) * (N.scale⁻¹ ^ 2 * _)
  have hs : N.scale ^ 2 * N.scale⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ N.scale_pos.ne', one_pow]
  calc
    _ = (N.scale ^ 2 * N.scale⁻¹ ^ 2) * R *
        roundCylinderPullback h (e ∘ N.coordinate_map) (M34.cylinderAxialTranslation c z) v w := by
      rw [hs, one_mul]
    _ = _ := by ring

end PoincareConjecture.EpsilonNeck
