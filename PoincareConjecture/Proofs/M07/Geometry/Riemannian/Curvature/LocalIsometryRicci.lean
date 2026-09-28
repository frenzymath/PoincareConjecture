import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem ricci_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = D'.ricci (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x (fun a b => (hmetric x hx a b).symm))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner (fun a b => (hmetric x hx a b).symm)
  have htrace := bilinear_sum_orthonormalBasis_eq
    (D'.curvatureTensor_bilinear_first_third (f x) (e u) (e v))
    ((g.orthonormalBasis x).map e') (h.orthonormalBasis (f x))
  change (∑ i, D'.curvatureTensor (f x)
      (e (g.orthonormalBasis x i)) (e u) (e (g.orthonormalBasis x i)) (e v)) =
    ∑ i, D'.curvatureTensor (f x)
      (h.orthonormalBasis (f x) i) (e u) (h.orthonormalBasis (f x) i) (e v) at htrace
  have hswap (a b : TangentSpace (𝓡 n) (f x)) :
      D'.curvatureTensor (f x) a (e u) b (e v) =
        D'.curvatureTensor (f x) (e u) a (e v) b := by
    rw [D'.curvatureTensor_swap_first, D'.curvatureTensor_swap_last, neg_neg]
  simp_rw [hswap] at htrace
  have hcurv (a b c d : TangentSpace (𝓡 n) x) :
      D'.curvatureTensor (f x) (e a) (e b) (e c) (e d) =
        D.curvatureTensor x a b c d :=
    (D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx a b c d).symm
  simp_rw [hcurv] at htrace
  simpa only [ricci, e, LinearEquiv.ofBijective_apply,
    ContinuousLinearMap.coe_coe] using htrace

theorem ricci_eq_of_eventually_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    {x : M} (hx : x ∈ U)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = D'.ricci (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp hmetric
  exact D.ricci_eq_of_local_isometry D' (hU.inter hVo)
    (hf.mono inter_subset_left) (fun y hy => hVsub hy.2) ⟨hx, hxV⟩ u v

end PoincareConjecture.LeviCivitaData
