import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawStage
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeInitialPair
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.PartialDiffeomorphPullback











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open PoincareConjecture.Proofs.M28.NeckTransfer

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 2400000 in





theorem exists_regularRawStage_forward_neck_geometry (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric) (j : ℕ), L.carrier ⊆ G.exhaustion j →
      L.center = G.base → ∀ theta : ℝ, L.epsilon ≤ theta → theta < 1 / 2 →
        ∀ k ≥ j, ∃ V : NeckGeometryCore
          ((E (phi (G.subsequence k) + H.shift)).flow.metric
            (E (phi (G.subsequence k) + H.shift)).time) theta,
          V.center = ((T (phi (G.subsequence k))).list.node 0).2.center ∧
          V.scale = ((T (phi (G.subsequence k))).list.node 0).2.scale ∧
          V.connection = ((T (phi (G.subsequence k))).list.node 0).2.connection ∧
          V.carrier = (H.regularRawStageDiffeomorph T A1 hA1 phi G k) ''
            L.region (-theta⁻¹) theta⁻¹ ∧
          V.central_sphere = (H.regularRawStageDiffeomorph T A1 hA1 phi G k) ''
            L.central_sphere ∧
          ∀ z : RoundCylinderSpace, V.coordinate_map z =
            H.regularRawStageDiffeomorph T A1 hA1 phi G k (L.coordinate_map z) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro L j hLstage hLcenter theta htheta hhalf k hjk
  let i := phi (G.subsequence k)
  let N := ((T i).list.node 0).2
  let e := H.regularRawStageDiffeomorph T A1 hA1 phi G k
  let R := L.restrict_m28 theta htheta hhalf
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  have hcap : R.carrier ⊆ e.symm.target := by
    change R.carrier ⊆ e.source
    rw [H.regularRawStageDiffeomorph_source]
    intro x hx
    exact hmono hjk (hLstage hx.1)
  have hcenter : e R.center = N.center := by
    change e L.center = N.center
    rw [hLcenter, H.regularRawStageDiffeomorph_base]
    exact (T i).node_zero_readout.2.2.symm
  have hscalar : 0 < N.connection.scalarCurvature (e.symm.symm R.center) := by
    change 0 < N.connection.scalarCurvature (e R.center)
    rw [hcenter]
    exact N.scalar_center_pos
  let V := pullbackNeckGeometry e.symm R hcap N.connection hscalar
  refine ⟨V, hcenter, ?_, rfl, rfl, rfl, fun _ => rfl⟩
  change (N.connection.scalarCurvature (e R.center)) ^ (-1 / 2 : ℝ) = N.scale
  rw [hcenter]
  exact N.scale_eq_scalar.symm

end PoincareConjecture.M28.CounterexampleNeckFamily
