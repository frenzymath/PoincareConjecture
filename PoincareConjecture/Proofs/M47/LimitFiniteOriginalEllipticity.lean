import PoincareConjecture.Proofs.M47.LimitFiniteOriginalSourceJets
import PoincareConjecture.Proofs.M47.LimitNoncollapseSharpMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteOriginalEllipticDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteOriginalEllipticDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteOriginalEllipticBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteOriginalEllipticBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

private theorem coefficient_pos
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    {z : E} (hz : z ∈ Φ.source) {v : E} (hv : v ≠ 0) :
    0 < g.pullbackCoefficients Φ z v v := by
  have hi : (mfderiv (𝓡 3) (𝓡 3) Φ z).IsInvertible :=
    ⟨(Φ.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hz).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  have hv' : mfderiv (𝓡 3) (𝓡 3) Φ z v ≠ 0 := by
    intro heq
    apply hv
    apply hi.injective
    simpa only [map_zero] using heq
  exact g.pos (Φ z) _ hv'

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteOriginalEllipticTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteOriginalEllipticCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteOriginalEllipticManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitFinite_original_source_ellipticity
    {d K R ρ : ℝ} (hd : 0 < d) (hK : 0 < K) (_hρ : 0 < ρ) (hρR : 2 * ρ < R)
    (hc : -H.toReal + d / 4 ∈ blowupBackwardInterval H) (j : ℕ)
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E
      (⟨G.exhaustion.space j, G.exhaustion.space_open j⟩ :
        TopologicalSpace.Opens G.limit.sliceCarrier.carrier) ∞)
    (hsource : Φ.source = Metric.ball 0 R) :
    let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
      ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ᶠ k : ℕ in atTop,
      ∀ ht : -H.toReal + d / 4 ∈ Icc (-G.exhaustion.time k) 0,
        ∀ A : RicciFlow 3 U (Icc (-(H.toReal + d / 2)) 0),
          (∀ s ∈ Icc (-(H.toReal + d / 2)) 0, ∀ x : U,
            |(A.connection s).curvatureTensorNorm x| ≤ K) →
          (∀ (x : U) (v w : TangentSpace (𝓡 3) x),
            (A.metric (-H.toReal + d / 4)).inner x v w =
              (G.embedding k).pullbackInner (-H.toReal + d / 4) ht x.val
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)) →
          ∀ s ∈ Icc (-(3 * d / 4)) 0, ∀ z ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
            a * ‖v‖ ^ 2 ≤ (A.metric (s + (-H.toReal + d / 4))).pullbackCoefficients
                Φ z v v ∧
              (A.metric (s + (-H.toReal + d / 4))).pullbackCoefficients Φ z v v ≤
                b * ‖v‖ ^ 2 := by
  let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
  let c := -H.toReal + d / 4
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let gU := (G.limit.flow.metric c).pullbackOfLocalDiffeomorph
    (Subtype.val : U → G.limit.sliceCarrier.carrier)
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U)
  let B0 : E → V := gU.pullbackCoefficients Φ
  have hPhi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ (Metric.ball 0 R) := by
    simpa only [hsource] using Φ.contMDiffOn
  have hB0 : ContDiffOn ℝ ∞ B0 (Metric.ball 0 R) := by
    intro z hz
    exact (gU.contDiffAt_pullbackCoefficients
      ((hPhi z hz).contMDiffAt (Metric.isOpen_ball.mem_nhds hz))).contDiffWithinAt
  have hclosed : Metric.closedBall (0 : E) (2 * ρ) ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hρR
  have hpos : ∀ z ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E, v ≠ 0 →
      0 < B0 z v v := by
    intro z hz v hv
    exact coefficient_pos gU Φ (hsource.symm ▸ hclosed hz) hv
  obtain ⟨a0, ha0, C, hC, hbase⟩ := terminalCurvature_compact_coefficient_bounds
    Metric.isOpen_ball (isCompact_closedBall (0 : E) (2 * ρ)) hclosed hB0 hpos 0
  have hupper (z : E) (hz : z ∈ Metric.closedBall 0 (2 * ρ)) (v : E) :
      B0 z v v ≤ C * ‖v‖ ^ 2 := by
    have hn : ‖B0 z‖ ≤ C := by
      have h := (hbase z hz).2.1 0 le_rfl
      rw [norm_iteratedFDeriv_zero] at h
      exact h
    calc
      B0 z v v ≤ ‖B0 z v v‖ := le_abs_self _
      _ ≤ ‖B0 z v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖B0 z‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (C * ‖v‖) * ‖v‖ := by gcongr
      _ = C * ‖v‖ ^ 2 := by ring
  let image := (fun z : E => (Φ z).val) '' Metric.closedBall 0 (2 * ρ)
  have himage : IsCompact image :=
    (isCompact_closedBall (0 : E) (2 * ρ)).image_of_continuousOn
      (continuous_subtype_val.comp_continuousOn (hPhi.continuousOn.mono hclosed))
  have hcompare := limitNoncollapse_generalized_compact_inner_comparison G himage c hc
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨(a0 / 2) * Real.exp (-54 * K * (3 * d / 4)),
    (3 * C / 2) * Real.exp (54 * K * (3 * d / 4)), by positivity, by positivity, ?_⟩
  filter_upwards [hcompare] with k hk ht A hcurv hread
  obtain ⟨A', hmetric, _hnorm, hraw, hzero, _hmem, _hclock⟩ :=
    limitFinite_endpoint_buffer_flow hd hc.1 A hcurv
  have hanchor : ∀ z ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
      (a0 / 2) * ‖v‖ ^ 2 ≤ (A'.metric 0).pullbackCoefficients Φ z v v ∧
        (A'.metric 0).pullbackCoefficients Φ z v v ≤ (3 * C / 2) * ‖v‖ ^ 2 := by
    intro z hz v
    have hcmp := hk.2.2 (Φ z).val (mem_image_of_mem _ hz)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z v)) ht
    rw [← hread (Φ z) (mfderiv (𝓡 3) (𝓡 3) Φ z v)
      (mfderiv (𝓡 3) (𝓡 3) Φ z v)] at hcmp
    change (1 - 1 / 2 : ℝ) * B0 z v v ≤ (A.metric c).pullbackCoefficients Φ z v v ∧
      (A.metric c).pullbackCoefficients Φ z v v ≤ (1 + 1 / 2 : ℝ) * B0 z v v at hcmp
    rw [hzero]
    constructor
    · nlinarith [(hbase z hz).2.2 v, hcmp.1]
    · nlinarith [hupper z hz v, hcmp.2]
  intro s hs z hz v
  have h := limitFinite_chart_closed_bounds (by linarith : 0 < 3 * d / 4) hK.le hρR
    A' Φ (fun t ht x _ => (le_abs_self _).trans (hraw t ht x)) hanchor hs hz v
  rw [hmetric s] at h
  exact h

end PoincareConjecture.M47
