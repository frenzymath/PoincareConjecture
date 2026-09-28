import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Regularity.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Limit.RicciConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle Topology
open Set Filter

universe u

namespace PoincareConjecture.GradientShrinkingSolitonData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem potential_contMDiff (S : GradientShrinkingSolitonData n M) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ S.potential := by
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
      0 < S.metric.pullbackCoefficients c.symm y v v := by
    intro y hy v hv
    change 0 < S.metric.inner (c.symm y)
      (mfderiv (𝓡 n) (𝓡 n) c.symm y v) (mfderiv (𝓡 n) (𝓡 n) c.symm y v)
    apply S.metric.pos
    intro hz
    exact hv ((hcinv y hy).injective (by simpa using hz))
  obtain ⟨gE, DE, V, hV, hpV, hVc, hmetric⟩ := RiemannianMetric.exists_local_realization
    hc hpc (S.metric.pullbackCoefficients c.symm) (S.metric.contDiffOn_chartCoefficients p)
    (fun y _ v w => S.metric.symm (c.symm y) _ _) hpos
  have hfcomp : ContDiffOn ℝ 2 (S.potential ∘ c.symm) V := by
    intro y hy
    exact ((S.potential_C2 (c.symm y)).comp y
      ((hcs.contMDiffAt (hc.mem_nhds (hVc hy))).of_le
        (by norm_cast : (2 : ℕ∞ω) ≤ ∞))).contDiffAt.contDiffWithinAt
  have heq (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V)
      (v w : TangentSpace (𝓡 n) y) :
      gE.inner y v w = S.metric.inner (c.symm y)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y v) (mfderiv (𝓡 n) (𝓡 n) c.symm y w) := by
    change gE.euclideanCoefficients y v w = _
    rw [hmetric y hy]
    rfl
  have hesscomp (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V)
      (v w : EuclideanSpace ℝ (Fin n)) :
      DE.hessian (S.potential ∘ c.symm) y v w =
        (1 / 2 : ℝ) * gE.inner y v w - DE.ricci y v w := by
    have hnat := DE.hessian_comp_of_metric_pullback_of_C2 S.connection
      (hcs.contMDiffAt (hc.mem_nhds (hVc hy)))
      (Filter.eventually_of_mem (hV.mem_nhds hy) fun z hz => hcinv z (hVc hz))
      (Filter.eventually_of_mem (hV.mem_nhds hy) fun z hz => heq z hz)
      (S.potential_C2 (c.symm y)) v w
    have hric := DE.ricci_eq_pullback_euclidean S.connection
      (hcs.contMDiffAt (hc.mem_nhds (hVc hy)))
      (Filter.eventually_of_mem (hV.mem_nhds hy) fun z hz => hcinv z (hVc hz))
      (Filter.eventually_of_mem (hV.mem_nhds hy) fun z hz => heq z hz) v w
    rw [hnat, hric, heq y hy v w]
    linarith [S.soliton_equation (c.symm y)
      (mfderiv (𝓡 n) (𝓡 n) c.symm y v) (mfderiv (𝓡 n) (𝓡 n) c.symm y w)]
  have hh : ∀ v w : EuclideanSpace ℝ (Fin n),
      ContDiffOn ℝ ∞ (fun y => DE.hessian (S.potential ∘ c.symm) y v w) V := by
    intro v w
    have hg : ContDiff ℝ ∞ (fun y => gE.euclideanCoefficients y v w) :=
      ((contDiff_iff_contDiffAt.mpr gE.contDiffAt_euclideanCoefficients).clm_apply
        contDiff_const).clm_apply contDiff_const
    have h : ContDiff ℝ ∞
        (fun y => (1 / 2 : ℝ) * gE.euclideanCoefficients y v w - DE.ricci y v w) :=
      (contDiff_const.mul hg).sub (DE.contDiff_ricci_const v w)
    exact h.contDiffOn.congr (fun y hy => hesscomp y hy v w)
  have hs := DE.contDiffOn_of_C2_hessian_smooth hV hfcomp hh
  rw [contMDiffAt_iff_source]
  simpa only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] using
    (hs.contDiffAt (hV.mem_nhds hpV)).contMDiffAt

end PoincareConjecture.GradientShrinkingSolitonData
