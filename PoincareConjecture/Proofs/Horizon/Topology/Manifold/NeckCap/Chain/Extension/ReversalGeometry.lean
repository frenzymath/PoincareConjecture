import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder.Reflection.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RoundCylinderReflection

theorem contMDiff_space :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ space :=
  contMDiff_fst.prodMk (contDiff_neg.contMDiff.comp contMDiff_snd)

theorem mfderiv_space_apply (z : RoundCylinderSpace) (v : RoundCylinderTangent z) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) space z v =
      (v.1, -v.2) := by
  unfold space
  erw [mfderiv_prodMk mdifferentiableAt_fst mdifferentiableAt_snd.neg]
  simp only [mfderiv_fst, mfderiv_neg, mfderiv_snd]
  rfl

theorem neg_mem_interval {epsilon t : ℝ}
    (ht : t ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) : -t ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
  constructor <;> linarith [ht.1, ht.2]

def domain (epsilon : ℝ) : NeckDomain epsilon ≃ₜ NeckDomain epsilon where
  toFun z := (z.1, ⟨-(z.2 : ℝ), neg_mem_interval z.2.property⟩)
  invFun z := (z.1, ⟨-(z.2 : ℝ), neg_mem_interval z.2.property⟩)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem roundCylinderPullback_comp (g : RiemannianMetric 3 M)
    (f : RoundCylinderSpace → M) :
    roundCylinderPullback g (f ∘ space) = pullback (roundCylinderPullback g f) := by
  funext z v w
  have hs (z : RoundCylinderSpace) :=
    contMDiff_space.mdifferentiable (by simp) z
  by_cases hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (space z)
  · simp only [roundCylinderPullback, pullback, mfderiv_comp z hf (hs z),
      ContinuousLinearMap.comp_apply, mfderiv_space_apply, Function.comp_apply]
  · have hcomp : ¬ MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (f ∘ space) z := by
      intro h
      have h'' : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          (f ∘ space) (space (space z)) := by simpa only [space_involutive] using h
      have h' := h''.comp (space z) (hs (space z))
      apply hf
      simpa only [Function.comp_def, space_involutive] using h'
    simp only [roundCylinderPullback, pullback, mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hcomp, zero_apply,
      map_zero]

end PoincareConjecture.RoundCylinderReflection
