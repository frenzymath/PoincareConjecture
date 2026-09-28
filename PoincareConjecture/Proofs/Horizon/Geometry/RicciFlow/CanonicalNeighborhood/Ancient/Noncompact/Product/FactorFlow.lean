import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.CurvatureSupplement
import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.FactorMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27SphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} (C : M27SphereLineFlowCertificate K)

theorem sphere_ricci {t : ℝ} (ht : t ≤ 0) (p : UnitTwoSphere × ℝ)
    (v w : TangentSpace (𝓡 2) p.1) :
    (K.flow.connection t).ricci (C.identification p)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.identification p (v, 0))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.identification p (w, 0)) =
        (C.sphere.connection t).ricci p.1 v w :=
  (C.sphere.metric t).ricci_eq_of_line_product (K.flow.metric t)
    (C.sphere.connection t) (K.flow.connection t) C.identification
    (C.metric_transport t ht) p v w

theorem sphere_equation {t : ℝ} (ht : t ≤ 0) (x : UnitTwoSphere)
    (v w : TangentSpace (𝓡 2) x) :
    HasDerivWithinAt (fun s => (C.sphere.metric s).inner x v w)
      (-2 * (C.sphere.connection t).ricci x v w) (Iic 0) t := by
  have he := K.flow.equation t ht (C.identification (x, 0))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.identification (x, 0) (v, 0))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.identification (x, 0) (w, 0))
  rw [C.sphere_ricci ht] at he
  apply he.congr
  · intro s hs
    simpa only [M27RoundSphereFamily.productInner, mul_zero, add_zero] using
      (C.metric_transport s hs (x, 0) (v, 0) (w, 0)).symm
  · simpa only [M27RoundSphereFamily.productInner, mul_zero, add_zero] using
      (C.metric_transport t ht (x, 0) (v, 0) (w, 0)).symm

theorem sphere_smooth : RiemannianMetric.IsSmoothFamilyOn C.sphere.metric (Iic 0) := by
  let i : UnitTwoSphere → M := fun x => C.identification (x, 0)
  have hi : ContMDiff (𝓡 2) (𝓡 3) ∞ i :=
    C.identification.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hid (x : UnitTwoSphere) (v : TangentSpace (𝓡 2) x) :
      mfderiv (𝓡 2) (𝓡 3) i x v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.identification (x, 0) (v, 0) := by
    change mfderiv (𝓡 2) (𝓡 3) (C.identification ∘ fun x => (x, 0)) x v = _
    erw [mfderiv_comp_apply _ (C.identification.contMDiff.mdifferentiable (by simp) _)
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const), mfderiv_prod_left]
    rfl
  have himm (x : UnitTwoSphere) : Function.Injective (mfderiv (𝓡 2) (𝓡 3) i x) := by
    intro v w hvw
    rw [hid, hid] at hvw
    have he := (C.identification.mfderivToContinuousLinearEquiv (by simp) (x, 0)).injective hvw
    exact congrArg Prod.fst he
  have hs := K.flow.smooth.pullbackImmersion i hi himm
  apply hs.congr
  rintro ⟨t, x⟩ ht
  congr 1
  ext v w
  change (C.sphere.metric t).inner x v w =
    (K.flow.metric t).inner (i x)
      (mfderiv (𝓡 2) (𝓡 3) i x v) (mfderiv (𝓡 2) (𝓡 3) i x w)
  rw [hid, hid]
  simpa only [M27RoundSphereFamily.productInner, mul_zero, add_zero] using
    (C.metric_transport t ht.1 (x, 0) (v, 0) (w, 0)).symm

def sphereFlow : RicciFlow 2 UnitTwoSphere (Iic 0) where
  metric := C.sphere.metric
  connection := C.sphere.connection
  interval := K.flow.interval
  nontrivial := K.flow.nontrivial
  smooth := C.sphere_smooth
  equation := fun _ ht x v w => C.sphere_equation ht x v w

end PoincareConjecture.M27SphereLineFlowCertificate
