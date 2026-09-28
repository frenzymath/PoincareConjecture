import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.EuclideanModel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Metric.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

local instance : ChartedSpace RoundCylinderCoordinates RoundCylinderSpace :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere ℝ ℝ

def roundCylinderProductMetric :
    Bundle.ContMDiffRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      RoundCylinderCoordinates (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
  RiemannianMetric.product
    (rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)
      2 (by norm_num)) RiemannianMetric.realLineMetric

@[simp] theorem roundCylinderProductMetric_inner (z : RoundCylinderSpace)
    (v w : RoundCylinderTangent z) :
    roundCylinderProductMetric.inner z v w = EvolvingRoundCylinderMetric 0 z v w := by
  rw [roundCylinderProductMetric, RiemannianMetric.product_inner, rescaledMetric_inner]
  simp only [Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner,
    RiemannianMetric.euclideanMetric_inner, EvolvingRoundCylinderMetric,
    sub_zero, mul_one]
  change _ + inner ℝ v.2 w.2 = _
  simp only [RCLike.inner_apply, conj_trivial]
  ring

def roundCylinderModelDiffeomorph :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ RoundCylinderSpace := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  refine { toEquiv := Equiv.refl _
           contMDiff_toFun := ?_
           contMDiff_invFun := ?_ }
  · change ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (id : RoundCylinderSpace → _)
    rw [← modelWithCornersSelf_prod]
    exact Poincare.Manifold.contMDiff_linearRechart_id (M := RoundCylinderSpace)
      (RiemannianMetric.lineModelEquiv 2)
  · change ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (id : RoundCylinderSpace → _)
    rw [← modelWithCornersSelf_prod]
    exact Poincare.Manifold.contMDiff_linearRechart_id_symm (M := RoundCylinderSpace)
      (RiemannianMetric.lineModelEquiv 2)

def roundCylinderMetric :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    RiemannianMetric 3 RoundCylinderSpace := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  apply RiemannianMetric.Induced.pullbackMetric roundCylinderProductMetric e.symm
    e.symm.contMDiff
  intro x
  have hh := mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) (e.symm x))
    (e.symm.contMDiff.mdifferentiable (by simp) x)
  have hid : (e : RoundCylinderSpace → RoundCylinderSpace) ∘ e.symm = id :=
    funext e.apply_symm_apply
  rw [hid, mfderiv_id] at hh
  exact Function.LeftInverse.injective (fun v => (congrArg (fun L => L v) hh).symm)

theorem roundCylinderMetric_inner :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    let e := roundCylinderModelDiffeomorph
    ∀ (z : RoundCylinderSpace) (v w : RoundCylinderTangent z),
      roundCylinderMetric.inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
      EvolvingRoundCylinderMetric 0 z v w := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  dsimp only
  intro z v w
  have hh := mfderiv_comp z (e.symm.contMDiff.mdifferentiable (by simp) (e z))
    (e.contMDiff.mdifferentiable (by simp) z)
  have hid : (e.symm : RoundCylinderSpace → RoundCylinderSpace) ∘ e = id :=
    funext e.symm_apply_apply
  rw [hid, mfderiv_id] at hh
  change roundCylinderProductMetric.inner (e.symm (e z))
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v))
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w)) = _
  have hv := congrArg (fun L => L v) hh
  have hw := congrArg (fun L => L w) hh
  change v = mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v) at hv
  change w = mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm (e z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) at hw
  rw [← hv, ← hw, e.symm_apply_apply, roundCylinderProductMetric_inner]

theorem roundCylinderMetric_inner_flat :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ∀ (z : RoundCylinderSpace) (v w : TangentSpace (𝓡 3) z),
      roundCylinderMetric.inner z v w = EvolvingRoundCylinderMetric 0 z
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) roundCylinderModelDiffeomorph.symm z v)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) roundCylinderModelDiffeomorph.symm z w) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  intro z v w
  exact roundCylinderProductMetric_inner z _ _

end PoincareConjecture
