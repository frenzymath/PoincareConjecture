import PoincareConjecture.Proofs.M47.LimitNoncollapseMetric
import PoincareConjecture.Proofs.M47.LimitNoncollapseCapture
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitNoncollapse_source_center_of_forward_bound
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (h0 : 0 ∈ I) (g : RiemannianMetric 3 C.carrier)
    (o x : C.carrier) (p : F.point) (hp : e.pointMap 0 h0 o = p)
    {r : ℝ} (hx : x ∈ g.ball o r) (hsource : g.ball o r ⊆ U)
    (hbound : ∀ y ∈ g.ball o r, ∀ v : TangentSpace (𝓡 3) y,
      e.pullbackInner 0 h0 y v v ≤ 2 * g.inner y v v) :
    ∃ y ∈ (F.metric p.1).ball p.2 (2 * r / Real.sqrt scale),
      e.pointMap 0 h0 x = (⟨p.1, y⟩ : F.point) := by
  subst p
  let f := e.spatialOpenPartialHomeomorph hU 0 h0
  let h := F.metric (origin + 0 / scale)
  have hC : 0 < 2 / Real.sqrt scale := div_pos two_pos (Real.sqrt_pos.mpr e.scale_pos)
  have himage := g.image_ball_subset_ball_of_tangentNorm_le h f o hC hsource
    (fun y hy => ((e.forward_smooth 0 h0 y hy).contMDiffAt
      (hU.mem_nhds hy)).of_le (by simp))
    (fun y hy v => limitNoncollapse_forward_tangent_bound g h v
      (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 h0) y v) e.scale_pos (hbound y hy v))
  refine ⟨e.forward 0 h0 x, ?_, rfl⟩
  have hmem := himage ⟨x, hx, rfl⟩
  have hr : (2 / Real.sqrt scale) * r = 2 * r / Real.sqrt scale := by ring
  change h.edist (e.forward 0 h0 o) (e.forward 0 h0 x) < _ at hmem ⊢
  simpa only [hr] using hmem

section Convergence

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

private local instance : TopologicalSpace C.limit.carrier.carrier :=
  C.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold

theorem limitNoncollapse_eventually_source_center (p : C.limit.sliceCarrier.carrier) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ k : ℕ in atTop,
      p ∈ C.exhaustion.space k ∧
      ∀ h0 : 0 ∈ Icc (-C.exhaustion.time k) 0,
        ∃ y ∈ S.baseBall (C.subsequence k) A,
          (C.embedding k).pointMap 0 h0 p =
            (⟨(S.base (C.subsequence k)).1, y⟩ : (S.flow (C.subsequence k)).point) := by
  let : T3Space C.limit.carrier.carrier := C.limit.carrier.t3Space
  let : ConnectedSpace C.limit.carrier.carrier := C.limit.connectedSpace
  let g := C.limit.flow.metric 0
  let r := (g.edist C.limit.base p).toReal + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hp : p ∈ g.ball C.limit.base r := by
    change g.edist C.limit.base p < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top C.limit.base p)]
    exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr (by dsimp only [r]; linarith)
  have hK : IsCompact (closure (g.ball C.limit.base r)) :=
    Proofs.M09.isCompact_closure_metric_ball g (C.limit.complete 0 C.limit.zero_mem)
      C.limit.base r
  refine ⟨2 * r, mul_pos two_pos hr, ?_⟩
  filter_upwards [limitNoncollapse_compact_inner_zero C hK] with k hk
  refine ⟨hk.1 (subset_closure hp), ?_⟩
  intro h0
  exact limitNoncollapse_source_center_of_forward_bound (C.embedding k)
    (C.exhaustion.space_open k) h0 g C.limit.base p (S.base (C.subsequence k))
    (C.base_preserving k h0) hp (fun _ hy => hk.1 (subset_closure hy))
    (fun y hy v => (hk.2 y (subset_closure hy) v).2)

end Convergence

end PoincareConjecture.M47
