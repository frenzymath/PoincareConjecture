import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.ReflectionJets
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.StandardGeometry.StandardNecks

/-!
# The actual differential of axial reflection

Morgan--Tian Definition 2.18, p. 31, and Remark 9.73, p. 231. The
opposite neck uses the exact reflected coordinate map. Its metric
pullback is the tensor reflection whose jet norm was already computed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.M45

local notation "I" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

/-- The opposite-neck map is a smooth involution. Definition 2.18, p. 31. -/
theorem cylinderAxialReflection_smooth :
    ContMDiff I I ∞ cylinderAxialReflection :=
  contMDiff_fst.prodMk contMDiff_snd.neg

/-- Axial reflection is its own inverse. Definition 2.18, p. 31. -/
@[simp] theorem cylinderAxialReflection_involutive (z : RoundCylinderSpace) :
    cylinderAxialReflection (cylinderAxialReflection z) = z := by
  simp [cylinderAxialReflection]

/-- The differential acts by the literal axial sign. Definition 2.18, p. 31. -/
theorem mfderiv_cylinderAxialReflection (z : RoundCylinderSpace)
    (v : RoundCylinderTangent z) :
    mfderiv I I cylinderAxialReflection z v = (v.1, -v.2) := by
  exact congrArg (fun L : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates => L v)
    ((hasMFDerivAt_fst z).prodMk (hasMFDerivAt_snd z).neg).mfderiv

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in
/-- The chain rule under reflection also holds for totalized derivatives
outside the neck domain, because reflection is a smooth involution.
Definition 2.18, p. 31. -/
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

/-- Pulling back by the opposite neck is exactly tensor reflection.
Definition 2.18, p. 31. -/
theorem roundCylinderPullback_reflection (g : RiemannianMetric 3 M)
    (f : RoundCylinderSpace → M) :
    roundCylinderPullback g (f ∘ cylinderAxialReflection) =
      cylinderReflectedTensor (roundCylinderPullback g f) := by
  funext z v w
  exact congrArg₂ (fun v w => g.inner (f (cylinderAxialReflection z)) v w)
    (mfderiv_comp_cylinderAxialReflection f z v)
    (mfderiv_comp_cylinderAxialReflection f z w)

/-- Every scalar multiple of an actual pullback is bilinear, including
where the derivative is totalized. Definition 2.16, p. 30. -/
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

/-- Exact metric comparison for the opposite neck, with no tolerance
change. Definitions 2.16 and 2.18, pp. 30-31. -/
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

end PoincareMT.M45
