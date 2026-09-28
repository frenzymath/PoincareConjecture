import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.CurvatureSupplement
import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.Evolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.LocalIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.FactorMetric












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]


def M27RoundSphereFamily.flowOfProductCover (S : M27RoundSphereFamily)
    (F : RicciFlow 3 M (Iic 0)) (f : UnitTwoSphere × ℝ → M)
    (hf : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f)
    (hmetric : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
      ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
      (F.metric t).inner (f p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f p w) = S.productInner t p v w) :
    RicciFlow 2 UnitTwoSphere (Iic 0) := by
  refine {
    metric := S.metric
    connection := S.connection
    interval := F.interval
    nontrivial := F.nontrivial
    smooth := ?_
    equation := ?_
  }
  · let i : UnitTwoSphere → M := fun x => f (x, 0)
    have hi : ContMDiff (𝓡 2) (𝓡 3) ∞ i :=
      hf.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
    have hid (x : UnitTwoSphere) (v : TangentSpace (𝓡 2) x) :
        mfderiv (𝓡 2) (𝓡 3) i x v =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (x, 0) (v, 0) := by
      change mfderiv (𝓡 2) (𝓡 3) (f ∘ fun x => (x, 0)) x v = _
      erw [mfderiv_comp_apply _ (hf.mdifferentiable (by simp) _)
        (mdifferentiableAt_id.prodMk mdifferentiableAt_const), mfderiv_prod_left]
      rfl
    have himm (x : UnitTwoSphere) : Function.Injective (mfderiv (𝓡 2) (𝓡 3) i x) := by
      intro v w hvw
      rw [hid, hid] at hvw
      exact congrArg Prod.fst ((hf.mfderivToContinuousLinearEquiv (by simp) (x, 0)).injective hvw)
    apply (F.smooth.pullbackImmersion i hi himm).congr
    rintro ⟨t, x⟩ ht
    congr 1
    ext v w
    change (S.metric t).inner x v w = (F.metric t).inner (i x)
      (mfderiv (𝓡 2) (𝓡 3) i x v) (mfderiv (𝓡 2) (𝓡 3) i x w)
    rw [hid, hid]
    simpa only [M27RoundSphereFamily.productInner, mul_zero, add_zero] using
      (hmetric t ht.1 (x, 0) (v, 0) (w, 0)).symm
  · intro t ht x v w
    have he := F.equation t ht (f (x, 0))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (x, 0) (v, 0))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (x, 0) (w, 0))
    rw [(S.metric t).ricci_eq_of_line_product_local_isometry (F.metric t)
      (S.connection t) (F.connection t) f hf.contMDiff (hmetric t ht)] at he
    apply he.congr
    · intro s hs
      simpa only [M27RoundSphereFamily.productInner, mul_zero, add_zero] using
        (hmetric s hs (x, 0) (v, 0) (w, 0)).symm
    · simpa only [M27RoundSphereFamily.productInner, mul_zero, add_zero] using
        (hmetric t ht (x, 0) (v, 0) (w, 0)).symm

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution 3 M}


def M27TwistedSphereLineFlowCertificate.sphereFlow
    (C : M27TwistedSphereLineFlowCertificate K) : RicciFlow 2 UnitTwoSphere (Iic 0) :=
  C.sphere.flowOfProductCover K.flow C.cover C.cover_local_diffeomorph C.metric_transport


def M27ProjectivePlaneLineFlowCertificate.sphereFlow
    (C : M27ProjectivePlaneLineFlowCertificate K) : RicciFlow 2 UnitTwoSphere (Iic 0) :=
  C.sphere.flowOfProductCover K.flow C.cover C.cover_local_diffeomorph C.metric_transport



theorem M27TwistedSphereLineFlowCertificate.sphere_inner_backward
    (C : M27TwistedSphereLineFlowCertificate K) {t u : ℝ} (ht : t ≤ 0) (hu : u ≤ 0)
    (p x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x) :
    (C.sphere.metric (t + u / (C.sphere.connection t).scalarCurvature p)).inner x v w =
      (1 - u) * (C.sphere.metric t).inner x v w :=
  RicciFlow.Splitting.round_surface_inner_backward C.sphereFlow C.sphere.round ht p hu x v w

end PoincareConjecture
