import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckJets
import PoincareConjecture.Proofs.M47.BlowupControlsCapSliceMap








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem cap_neck_image_tensor_difference {X : Type u} [TopologicalSpace X]
    [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 E} (N : EpsilonNeck g) (h : RiemannianMetric 3 X)
    {f : E → X} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) (hNU : N.carrier ⊆ U)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ x ∈ U, ∀ v w : E,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) = A x v w)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback h (f ∘ N.coordinate_map) z v w -
      roundCylinderPullback g N.coordinate_map z v w =
        (A (N.coordinate_map z) - g.euclideanCoefficients (N.coordinate_map z))
          (mfderiv Ic (𝓡 3) N.coordinate_map z v)
          (mfderiv Ic (𝓡 3) N.coordinate_map z w) := by
  have hx := hNU (N.coordinate_map_mem_of_axial_mem hz)
  have hcoord := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have htarget := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  unfold roundCylinderPullback
  rw [mfderiv_comp z htarget hcoord]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, sub_apply]
  rw [hA _ hx]
  rfl



theorem cap_neck_image_coefficient_difference {X : Type u} [TopologicalSpace X]
    [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 E} (N : EpsilonNeck g) (h : RiemannianMetric 3 X)
    {f : E → X} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) (hNU : N.carrier ⊆ U)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ x ∈ U, ∀ v w : E,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) = A x v w)
    (q : UnitTwoSphere) {y : RoundCylinderCoordinates}
    (hy : y.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (i l : Fin 3) :
    roundCylinderTensorCoefficient (roundCylinderPullback h (f ∘ N.coordinate_map))
        (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
        (chartAt E₂ q) y i l =
      roundCylinderTensorCoefficient
        (fun z v w => (A (N.coordinate_map z) - g.euclideanCoefficients (N.coordinate_map z))
          (mfderiv Ic (𝓡 3) N.coordinate_map z v)
          (mfderiv Ic (𝓡 3) N.coordinate_map z w)) (chartAt E₂ q) y i l :=
  cap_neck_image_tensor_difference N h hU hf hNU A hA hy _ _

end PoincareConjecture.M47
