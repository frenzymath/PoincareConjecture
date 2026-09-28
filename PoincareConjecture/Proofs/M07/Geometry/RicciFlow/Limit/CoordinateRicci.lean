import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.RicciConvergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace RiemannianMetric

private theorem exists_local_chart_realization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (x : M) :
    ∃ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g'),
      ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x),
        g'.euclideanCoefficients y =
          g.pullbackCoefficients (extChartAt (𝓡 n) x).symm y := by
  let c := extChartAt (𝓡 n) x
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨g', D, V, hVo, hpV, _, heq⟩ :=
    exists_local_realization (isOpen_extChartAt_target x) (mem_extChartAt_target x)
      (g.pullbackCoefficients c.symm)
      (fun y hy => (g.contDiffAt_pullbackCoefficients (hc y hy)).contDiffWithinAt)
      (fun y _ v w => g.symm (c.symm y) _ _)
      (fun y hy v hv => by
        apply g.pos (c.symm y)
        intro hzero
        apply hv
        apply (hi y hy).injective
        rw [map_zero]
        convert! hzero using 1)
  exact ⟨g', D, Filter.mem_of_superset (hVo.mem_nhds hpV) heq⟩

end RiemannianMetric

namespace LeviCivitaData



theorem tendsto_ricci_of_coordinate_jets
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n M} {g : RiemannianMetric n M}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (x : M) (u v : TangentSpace (𝓡 n) x)
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin n,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).pullbackCoefficients (extChartAt (𝓡 n) x).symm y
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) (extChartAt (𝓡 n) x x)) l
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => g.pullbackCoefficients (extChartAt (𝓡 n) x).symm y
            (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b)) (extChartAt (𝓡 n) x x)))) :
    Tendsto (fun i => (Dseq i).ricci x u v) l (𝓝 (D.ricci x u v)) := by
  classical
  let c := extChartAt (𝓡 n) x
  let p := c x
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  choose G DG hG using fun i => (gseq i).exists_local_chart_realization x
  obtain ⟨H, DH, hH⟩ := g.exists_local_chart_realization x
  have hjet (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (g'' : RiemannianMetric n M)
      (heq : ∀ᶠ y in 𝓝 p, g'.euclideanCoefficients y =
        g''.pullbackCoefficients c.symm y)
      (r : ℕ) (a d : Fin n) :
      iteratedFDeriv ℝ r (fun y => g'.inner y (b a) (b d)) p =
        iteratedFDeriv ℝ r
          (fun y => g''.pullbackCoefficients c.symm y (b a) (b d)) p := by
    have heq' : (fun y => g'.inner y (b a) (b d)) =ᶠ[𝓝 p]
        (fun y => g''.pullbackCoefficients c.symm y (b a) (b d)) := by
      filter_upwards [heq] with y hy
      exact congrArg (fun B => B (b a) (b d)) hy
    exact (heq'.iteratedFDeriv ℝ r).self_of_nhds
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm p :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
        (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hi : ∀ᶠ y in 𝓝 p, (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)]
      with y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨e, he⟩ := hi.self_of_nhds
  have hp : c.symm p = x := (extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)
  have hricci (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (g'' : RiemannianMetric n M) (D' : LeviCivitaData g') (D'' : LeviCivitaData g'')
      (heq : ∀ᶠ y in 𝓝 p, g'.euclideanCoefficients y =
        g''.pullbackCoefficients c.symm y) :
      D'.ricci p (e.symm u) (e.symm v) = D''.ricci x u v := by
    have hm : ∀ᶠ y in 𝓝 p, ∀ w z : EuclideanSpace ℝ (Fin n),
        g'.inner y w z = g''.inner (c.symm y)
          (mfderiv (𝓡 n) (𝓡 n) c.symm y w)
          (mfderiv (𝓡 n) (𝓡 n) c.symm y z) := by
      filter_upwards [heq] with y hy w z
      exact congrArg (fun B => B w z) hy
    have hnat := D'.ricci_eq_pullback_euclidean D'' hc hi hm (e.symm u) (e.symm v)
    simp only [← he, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] at hnat
    exact hnat.trans (congrArg (fun z => D''.ricci z
      (show EuclideanSpace ℝ (Fin n) from u)
      (show EuclideanSpace ℝ (Fin n) from v)) hp)
  have hlimit := tendsto_ricci_of_scalar_metric_jets (l := l) DG DH p
    (e.symm u) (e.symm v) b.toBasis
    (fun r hr a d => by
      change Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (G i).inner y (b a) (b d)) p) l
          (𝓝 (iteratedFDeriv ℝ r (fun y => H.inner y (b a) (b d)) p))
      rw [show (fun i => iteratedFDeriv ℝ r
          (fun y => (G i).inner y (b a) (b d)) p) =
          (fun i => iteratedFDeriv ℝ r
            (fun y => (gseq i).pullbackCoefficients c.symm y (b a) (b d)) p)
          from funext (fun i => hjet (G i) (gseq i) (hG i) r a d), hjet H g hH r a d]
      exact h r hr a d)
  simpa only [hricci (G _) _ (DG _) (Dseq _) (hG _), hricci H _ DH D hH] using hlimit

end LeviCivitaData

end PoincareConjecture
