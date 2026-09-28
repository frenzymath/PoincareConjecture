import PoincareConjecture.Proofs.M45.Ch9_Models.ReflectionJets
import PoincareConjecture.Proofs.M45.Ch12_Standard.StandardNecks









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M45

local notation "I" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


theorem cylinderAxialReflection_smooth :
    ContMDiff I I ∞ cylinderAxialReflection :=
  contMDiff_fst.prodMk contMDiff_snd.neg


@[simp] theorem cylinderAxialReflection_involutive (z : RoundCylinderSpace) :
    cylinderAxialReflection (cylinderAxialReflection z) = z := by
  simp [cylinderAxialReflection]


theorem mfderiv_cylinderAxialReflection (z : RoundCylinderSpace)
    (v : RoundCylinderTangent z) :
    mfderiv I I cylinderAxialReflection z v = (v.1, -v.2) := by
  exact congrArg (fun L : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates => L v)
    ((hasMFDerivAt_fst z).prodMk (hasMFDerivAt_snd z).neg).mfderiv

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in



theorem mfderiv_comp_cylinderAxialReflection (f : RoundCylinderSpace → M)
    (z : RoundCylinderSpace) (v : RoundCylinderTangent z) :
    mfderiv I (𝓡 3) (f ∘ cylinderAxialReflection) z v =
      mfderiv I (𝓡 3) f (cylinderAxialReflection z) (v.1, -v.2) := by
  have hR := cylinderAxialReflection_smooth.mdifferentiable (by simp)
  by_cases hf : MDifferentiableAt I (𝓡 3) f (cylinderAxialReflection z)
  · rw [mfderiv_comp_apply z hf (hR z), mfderiv_cylinderAxialReflection]
  · have hcomp : ¬MDifferentiableAt I (𝓡 3) (f ∘ cylinderAxialReflection) z := by
      intro h
      have h' := h.comp_of_eq (cylinderAxialReflection z) (hR (cylinderAxialReflection z))
        (cylinderAxialReflection_involutive z)
      apply hf
      simpa only [Function.comp_def, cylinderAxialReflection_involutive] using h'
    rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hcomp]
    rfl



theorem roundCylinderPullback_reflection (g : RiemannianMetric 3 M)
    (f : RoundCylinderSpace → M) :
    roundCylinderPullback g (f ∘ cylinderAxialReflection) =
      cylinderReflectedTensor (roundCylinderPullback g f) := by
  funext z v w
  exact congrArg₂ (fun v w => g.inner (f (cylinderAxialReflection z)) v w)
    (mfderiv_comp_cylinderAxialReflection f z v)
    (mfderiv_comp_cylinderAxialReflection f z w)



theorem roundCylinderPullback_bilinear (g : RiemannianMetric 3 M)
    (f : RoundCylinderSpace → M) (c : ℝ) (z : RoundCylinderSpace) :
    IsBilinearMap ℝ (fun v w => c * roundCylinderPullback g f z v w) := by
  constructor
  · intro v w q
    simp only [roundCylinderPullback, map_add, add_apply, mul_add]
  · intro a v w
    simp only [roundCylinderPullback, map_smul, smul_apply, smul_eq_mul]
    ring
  · intro v w q
    simp only [roundCylinderPullback, map_add, mul_add]
  · intro a v w
    simp only [roundCylinderPullback, map_smul, smul_eq_mul]
    ring



theorem neckMetricComparison_reflection (g : RiemannianMetric 3 M)
    {epsilon scale : ℝ} {f : RoundCylinderSpace → M}
    (h : NeckMetricJetComparison g epsilon scale f) :
    NeckMetricJetComparison g epsilon scale (f ∘ cylinderAxialReflection) := by
  refine ⟨?_⟩
  have heq : (fun z v w => scale⁻¹ ^ 2 *
      roundCylinderPullback g (f ∘ cylinderAxialReflection) z v w) =
      cylinderReflectedTensor (fun z v w => scale⁻¹ ^ 2 *
        roundCylinderPullback g f z v w) := by
    rw [roundCylinderPullback_reflection]
    rfl
  rw [heq]
  exact cylinderReflectedTensor_close (by norm_num) _
    (roundCylinderPullback_bilinear g f _) h.close

end PoincareConjecture.M45
