import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

private theorem exists_chart_metric_realization (g : RiemannianMetric n M) (x : M) :
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (_D : LeviCivitaData gE),
      ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x), ∀ u v : EuclideanSpace ℝ (Fin n),
        gE.inner y u v = g.inner ((extChartAt (𝓡 n) x).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y u)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y v) := by
  let c := extChartAt (𝓡 n) x
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨gE, DE, V, hVo, hpV, _, heq⟩ :=
    RiemannianMetric.exists_local_realization (isOpen_extChartAt_target x)
      (mem_extChartAt_target x) (g.pullbackCoefficients c.symm)
      (fun y hy => (g.contDiffAt_pullbackCoefficients (hc y hy)).contDiffWithinAt)
      (fun y _ u v => g.symm (c.symm y) _ _)
      (fun y hy v hv => by
        apply g.pos (c.symm y)
        intro hzero
        apply hv
        apply (hi y hy).injective
        rw [map_zero]
        convert! hzero using 1)
  refine ⟨gE, DE, ?_⟩
  filter_upwards [hVo.mem_nhds hpV] with y hy u v
  exact congrArg (fun B => B u v) (heq y hy)

namespace LeviCivitaData

private theorem curvature_and_norm_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    (∀ u v w z : TangentSpace (𝓡 n) x,
      D.curvatureTensor x u v w z = D'.curvatureTensor (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v)
        (mfderiv (𝓡 n) (𝓡 n) f x w) (mfderiv (𝓡 n) (𝓡 n) f x z)) ∧
      D.curvatureTensorNorm x = D'.curvatureTensorNorm (f x) := by
  let c := extChartAt (𝓡 n) x
  let p := c x
  have hp : c.symm p = x := c.left_inv (mem_extChartAt_source x)
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hcp := hc p (mem_extChartAt_target x)
  have hi : ∀ᶠ y in 𝓝 p, (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x)] with y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  have hW : ∀ᶠ y in 𝓝 p, y ∈ c.target ∧ c.symm y ∈ U := by
    have hpre := hcp.continuousAt.preimage_mem_nhds (hU.mem_nhds (hp.symm ▸ hx))
    exact inter_mem (extChartAt_target_mem_nhds' (mem_extChartAt_target x)) hpre
  have hderiv (y : EuclideanSpace ℝ (Fin n))
      (hy : y ∈ c.target ∧ c.symm y ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y =
        (mfderiv (𝓡 n) (𝓡 n) f (c.symm y)).comp
          (mfderiv (𝓡 n) (𝓡 n) c.symm y) :=
    mfderiv_comp y (((hf _ hy.2).contMDiffAt (hU.mem_nhds hy.2)).mdifferentiableAt
      (by simp)) ((hc y hy.1).mdifferentiableAt (by simp))
  obtain ⟨gE, DE, hE⟩ := exists_chart_metric_realization g x
  have hEf : ∀ᶠ y in 𝓝 p, ∀ u v : EuclideanSpace ℝ (Fin n),
      gE.inner y u v = h.inner ((f ∘ c.symm) y)
        (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y u)
        (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y v) := by
    filter_upwards [hW, hE] with y hy he u v
    rw [hderiv y hy, he, hmetric _ hy.2]
    rfl
  have hif : ∀ᶠ y in 𝓝 p, (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y).IsInvertible := by
    filter_upwards [hEf] with y hy
    have hb := gE.mfderiv_bijective_of_pullback_eq h y (fun u v => (hy u v).symm)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) y) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) _
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) ((f ∘ c.symm) y)) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : N → Type _) _
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ c.symm) y).toLinearMap hb).toContinuousLinearEquiv,
      rfl⟩
  have hcf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (f ∘ c.symm) p :=
    ((hf _ hW.self_of_nhds.2).contMDiffAt (hU.mem_nhds hW.self_of_nhds.2)).comp p hcp
  constructor
  · obtain ⟨e, he⟩ := hi.self_of_nhds
    intro u v w z
    have hg := DE.curvatureTensor_eq_pullback_euclidean D hcp hi hE
      (e.symm u) (e.symm v) (e.symm w) (e.symm z)
    have hh := DE.curvatureTensor_eq_pullback_euclidean D' hcf hif hEf
      (e.symm u) (e.symm v) (e.symm w) (e.symm z)
    have heq := hg.symm.trans hh
    rw [hderiv p hW.self_of_nhds, ← he] at heq
    change D.curvatureTensor (c.symm p)
      (e (e.symm u)) (e (e.symm v)) (e (e.symm w)) (e (e.symm z)) =
        D'.curvatureTensor (f (c.symm p))
          (mfderiv (𝓡 n) (𝓡 n) f (c.symm p) (e (e.symm u)))
          (mfderiv (𝓡 n) (𝓡 n) f (c.symm p) (e (e.symm v)))
          (mfderiv (𝓡 n) (𝓡 n) f (c.symm p) (e (e.symm w)))
          (mfderiv (𝓡 n) (𝓡 n) f (c.symm p) (e (e.symm z))) at heq
    simp only [ContinuousLinearEquiv.apply_symm_apply] at heq
    exact (congrArg (fun y =>
      D.curvatureTensor y (show EuclideanSpace ℝ (Fin n) from u)
        (show EuclideanSpace ℝ (Fin n) from v) (show EuclideanSpace ℝ (Fin n) from w)
        (show EuclideanSpace ℝ (Fin n) from z) =
      D'.curvatureTensor (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y (show EuclideanSpace ℝ (Fin n) from u))
        (mfderiv (𝓡 n) (𝓡 n) f y (show EuclideanSpace ℝ (Fin n) from v))
        (mfderiv (𝓡 n) (𝓡 n) f y (show EuclideanSpace ℝ (Fin n) from w))
        (mfderiv (𝓡 n) (𝓡 n) f y (show EuclideanSpace ℝ (Fin n) from z))) hp).mp heq
  · have hg := DE.curvatureTensorNorm_eq_pullback_euclidean D hcp hi hE
    have hh := DE.curvatureTensorNorm_eq_pullback_euclidean D' hcf hif hEf
    simpa only [Function.comp_apply, hp] using hg.symm.trans hh



theorem curvatureTensor_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = D'.curvatureTensor (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (mfderiv (𝓡 n) (𝓡 n) f x w) (mfderiv (𝓡 n) (𝓡 n) f x z) :=
  (curvature_and_norm_eq_of_local_isometry D D' hU hf hmetric hx).1 u v w z



theorem curvatureTensorNorm_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm (f x) :=
  (curvature_and_norm_eq_of_local_isometry D D' hU hf hmetric hx).2

end LeviCivitaData

end PoincareConjecture
