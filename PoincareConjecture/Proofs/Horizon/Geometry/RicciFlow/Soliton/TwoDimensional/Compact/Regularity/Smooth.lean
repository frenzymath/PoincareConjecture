import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle Topology
open Set Filter

universe u

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem contMDiff_of_C2_hessian_eq_smooth_mul_metric (D : LeviCivitaData g)
    {f a : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f)
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hess : ∀ x, ∀ v w : TangentSpace (𝓡 n) x,
      D.hessian f x v w = a x * g.inner x v w) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := by
  intro p
  let c := extChartAt (𝓡 n) p
  have hc : IsOpen c.target := isOpen_extChartAt_target p
  have hpc : c p ∈ c.target := mem_extChartAt_target p
  have hcs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm p
  have hcinv (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) (x := p) hy)
  have hpos : ∀ y ∈ c.target, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < g.pullbackCoefficients c.symm y v v := by
    intro y hy v hv
    change 0 < g.inner (c.symm y)
      (mfderiv (𝓡 n) (𝓡 n) c.symm y v) (mfderiv (𝓡 n) (𝓡 n) c.symm y v)
    apply g.pos
    intro hz
    exact hv ((hcinv y hy).injective (by simpa using hz))
  obtain ⟨gE, DE, V, hV, hpV, hVc, hmetric⟩ := RiemannianMetric.exists_local_realization hc hpc
    (g.pullbackCoefficients c.symm) (g.contDiffOn_chartCoefficients p)
    (fun y _ v w => g.symm (c.symm y) _ _) hpos
  have hfcomp : ContDiffOn ℝ 2 (f ∘ c.symm) V := by
    intro y hy
    exact ((hf (c.symm y)).comp y
      ((hcs.contMDiffAt (hc.mem_nhds (hVc hy))).of_le
        (by norm_cast : (2 : ℕ∞ω) ≤ ∞))).contDiffAt.contDiffWithinAt
  have hacomp : ContDiffOn ℝ ∞ (a ∘ c.symm) V := by
    intro y hy
    exact ((ha (c.symm y)).comp y
      (hcs.contMDiffAt (hc.mem_nhds (hVc hy)))).contDiffAt.contDiffWithinAt
  have heq (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V)
      (v w : TangentSpace (𝓡 n) y) :
      gE.inner y v w = g.inner (c.symm y)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y v) (mfderiv (𝓡 n) (𝓡 n) c.symm y w) := by
    change gE.euclideanCoefficients y v w = _
    rw [hmetric y hy]
    rfl
  have hesscomp : ∀ y ∈ V, ∀ v w,
      DE.hessian (f ∘ c.symm) y v w = (a ∘ c.symm) y * gE.inner y v w := by
    intro y hy v w
    have hnat := DE.hessian_comp_of_metric_pullback_of_C2 D
      (hcs.contMDiffAt (hc.mem_nhds (hVc hy)))
      (Filter.eventually_of_mem (hV.mem_nhds hy) fun z hz => hcinv z (hVc hz))
      (Filter.eventually_of_mem (hV.mem_nhds hy) fun z hz => heq z hz)
      (hf (c.symm y)) v w
    rw [hnat, hess, ← heq y hy v w]
    rfl
  have hs := DE.contDiffOn_of_C2_hessian_eq_smooth_mul_metric hV hfcomp hacomp hesscomp
  rw [contMDiffAt_iff_source]
  simpa only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] using
    (hs.contDiffAt (hV.mem_nhds hpV)).contMDiffAt

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem potential_smooth (S : GradientShrinkingSolitonData 2 M) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ S.potential := by
  apply S.connection.contMDiff_of_C2_hessian_eq_smooth_mul_metric S.potential_C2
    (a := fun x => (1 - S.connection.scalarCurvature x) / 2)
  · exact (contMDiff_const.sub S.connection.contMDiff_scalarCurvature).div_const 2
  · exact S.hessian_potential_eq_scalar

end PoincareConjecture.GradientShrinkingSolitonData
