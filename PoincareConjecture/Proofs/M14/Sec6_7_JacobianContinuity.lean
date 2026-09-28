import PoincareConjecture.Proofs.M14.Sec6_7_PullbackJacobian

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
  {H : M14StableSet G T τ x E}

theorem measureData_jacobian_continuousOn (D : M14MeasureJacobianData G T τ x E H) :
    ContinuousOn D.jacobian H.carrier := by
  let : T2Space (G.Horizontal x) :=
    FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let C := D.sourceBasis.euclideanCoordinates
  let e := stableCoordinateChart H D.sourceBasis
  let ρ := M10.pullbackJacobian (G.slices (T - τ)).metricOnPoints e
  have he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source :=
    (stableCoordinateChart_smooth H D.sourceBasis).of_le (by simp)
  have hρ : ContinuousOn ρ e.source := by
    intro z hz
    exact (M10.pullbackJacobian_continuousAt (G.slices (T - τ)).metricOnPoints
      (he.contMDiffAt (e.open_source.mem_nhds hz))).continuousWithinAt
  have hmap : Set.MapsTo C.symm H.carrier e.source := by
    intro Z hZ
    change C (C.symm Z) ∈ H.carrier
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hZ
  apply (hρ.comp C.symm.continuous.continuousOn hmap).congr
  intro Z hZ
  have hpre : D.sourceBasis.euclideanCoordinates (C.symm Z) ∈ H.carrier := hmap hZ
  have hpull := pullbackJacobian_eq_metricJacobian H D.sourceBasis D.targetBasis
    (C.symm Z) hpre
  have hpull' : ρ (C.symm Z) =
      M14MetricJacobianFromBasis G D.sourceBasis D.targetBasis Z hZ := by
    simpa only [C, e, ρ, ContinuousLinearEquiv.apply_symm_apply] using hpull
  exact (D.jacobian_eq Z hZ).trans hpull'.symm

end PoincareConjecture.M14
