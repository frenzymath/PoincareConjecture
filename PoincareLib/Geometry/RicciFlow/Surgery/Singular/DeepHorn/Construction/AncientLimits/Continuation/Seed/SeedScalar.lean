import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.LimitGeometry.Charts.SliceCurvatureComparison
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.LimitGeometry.Charts.InverseConfinement
import PoincareLib.Geometry.Riemannian.Curvature.Scalar.SharpBounds

/-!
# One terminal scalar bound before the spatial radius

Morgan--Tian Claim 11.35 and its continuation, printed pp. 289-291.
The actual limit's compact-time curvature bound at the singleton zero
gives one scalar bound. Actual scalar convergence and inverse-ball
confinement transfer it to every fixed ball on the one retained sequence.

The zero-clock identity rederives the private `cylinderSliceAt_pointMap`
in owned ZeroSlice. Its read-only DeepHorn/Limit/NeckTransfer donor is
`GeneralizedFlowCylinder.sliceHomeomorphAt_pointMap`. The confinement
donor is `GeneralizedBlowupConvergence.eventually_baseBall_subset_zeroSliceEmbedding_image_ball`
in DeepHorn/Limit/MetricTransfer. Only the owned replacements are imported.
Reviewed derivation: `claim11_35-positive-seed.md`, section 1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

private theorem seed_zeroSliceEmbedding_pointMap_eq
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ)
    (hzero : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0)
    (x : G.limit.carrier.carrier) :
    (G.embedding k).pointMap 0 hzero x =
      (⟨(S.base (G.subsequence k)).1, blowup_zeroSliceEmbedding G k x⟩ :
        (S.flow (G.subsequence k)).point) := by
  have hcast {F : GeneralizedRicciFlowData.{u}} {C : Type u}
      [TopologicalSpace C] {a b : ℝ}
      (e : OpenPartialHomeomorph C (F.slice a).carrier) (h : a = b) (z : C) :
      (⟨a, e z⟩ : F.point) = ⟨b, (h ▸ e) z⟩ := by
    cases h
    rfl
  let e : OpenPartialHomeomorph G.limit.sliceCarrier.carrier
      ((S.flow (G.subsequence k)).slice
        ((S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k))).carrier := {
    toFun := (G.embedding k).forward 0 hzero
    invFun := (G.embedding k).inverse 0 hzero
    source := G.exhaustion.space k
    target := (G.embedding k).forward 0 hzero '' G.exhaustion.space k
    map_source' := fun z hz => mem_image_of_mem _ hz
    map_target' := by
      rintro z ⟨y, hy, rfl⟩
      rw [(G.embedding k).left_inverse 0 hzero hy]
      exact hy
    left_inv' := (G.embedding k).left_inverse 0 hzero
    right_inv' := (G.embedding k).right_inverse 0 hzero
    open_source := G.exhaustion.space_open k
    open_target := cylinder_isOpen_forward_image (G.embedding k)
      (G.exhaustion.space_open k) 0 hzero
    continuousOn_toFun := ((G.embedding k).forward_smooth 0 hzero).continuousOn
    continuousOn_invFun := ((G.embedding k).inverse_smooth 0 hzero).continuousOn }
  exact hcast e (by simp) x

/-- One actual terminal scalar bound works on every fixed source ball
of the retained subsequence. Its constant precedes the radius, as in
Claim 11.35 and the continuation, printed pp. 289-291. -/
theorem blowup_exists_uniform_terminal_scalar_bound
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) :
    ∃ M : ℝ, 0 < M ∧ ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ S.baseBall (G.subsequence k) A,
        (S.flow (G.subsequence k)).scalar ⟨(S.base (G.subsequence k)).1, x⟩ ≤
          M * S.scale (G.subsequence k) := by
  obtain ⟨B₀, hB₀, hbound⟩ := G.limit.curvature_locally_bounded_in_time
    {0} isCompact_singleton (singleton_subset_iff.mpr G.limit.zero_mem)
  have hscalar (x : G.limit.carrier.carrier) :
      (G.limit.flow.connection 0).scalarCurvature x ≤ 3 * B₀ := by
    have hnorm := (le_abs_self ((G.limit.flow.connection 0).curvatureTensorNorm x)).trans
      (hbound 0 (mem_singleton 0) x)
    exact ((G.limit.flow.connection 0).scalarCurvature_le_curvatureTensorNorm_sharp x).trans
      (mul_le_mul_of_nonneg_left hnorm (by norm_num))
  refine ⟨3 * B₀ + 1, by positivity, ?_⟩
  intro A hA
  let g := G.limit.flow.metric 0
  let K : Set G.limit.carrier.carrier :=
    {z | g.edist G.limit.base z ≤ ENNReal.ofReal (2 * A + 1)}
  have hK : IsCompact K := g.isCompact_closedBall_of_metricComplete
    (G.limit.complete 0 G.limit.zero_mem) G.limit.base (2 * A + 1)
  filter_upwards [blowup_eventually_baseBall_subset_zeroSliceEmbedding_image_ball
    G hA (by norm_num : (1 : ℝ) < 2),
    blowup_eventually_sliceScalar_error G G.limit.zero_mem hK
      (by norm_num : (0 : ℝ) < 1)] with k hcover hconvergence x hx
  obtain ⟨z, hz, rfl⟩ := hcover hx
  have hzK : z ∈ K := (show g.edist G.limit.base z < ENNReal.ofReal (2 * A) from hz).le.trans
    (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨hzero, _hsource, herr⟩ := hconvergence
  have h := (abs_lt.mp (herr z hzK)).2
  rw [seed_zeroSliceEmbedding_pointMap_eq G k hzero z] at h
  have hq : 0 < S.scale (G.subsequence k) := S.base_scalar_pos (G.subsequence k)
  apply (div_le_iff₀ hq).mp
  linarith [hscalar z]

end PoincareMT.M32
