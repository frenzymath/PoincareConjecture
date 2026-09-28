import PoincareConjecture.Proofs.M47.LimitFiniteAnchorCoefficients
import PoincareConjecture.Proofs.M47.TerminalCurvatureCompactCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteAnchorJetsDualAdd : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteAnchorJetsDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteAnchorJetsBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteAnchorJetsBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence S J)

private local instance finiteAnchorJetsTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance finiteAnchorJetsCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance finiteAnchorJetsManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem limitFinite_exists_original_anchor_bounds (P : M47Predecessors.{u})
    (c : ℝ) (hc : c ∈ J) (j : ℕ)
    (q : G.limit.sliceCarrier.carrier) (hq : q ∈ G.exhaustion.space j) :
    let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
      ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
    ∃ R ρ : ℝ, 0 < ρ ∧ 2 * ρ < R ∧
      ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
        Φ.source = Metric.ball 0 R ∧ Φ 0 = ⟨q, hq⟩ ∧
        (∀ z ∈ Metric.ball 0 R,
          (Φ z).val = (extChartAt (𝓡 3) q).symm ((extChartAt (𝓡 3) q) q + z)) ∧
        ∃ a0 b0 : ℝ, 0 < a0 ∧ 0 ≤ b0 ∧
          ∀ m : ℕ, ∃ Z : ℝ, 1 ≤ Z ∧ ∀ᶠ k : ℕ in atTop,
            ∃ ht : c ∈ Icc (-G.exhaustion.time k) 0,
              G.exhaustion.space j ⊆ G.exhaustion.space k ∧
              ∀ g : RiemannianMetric 3 U,
                (∀ (x : U) (v w : TangentSpace (𝓡 3) x),
                  g.inner x v w = (G.embedding k).pullbackInner c ht x.val
                    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)) →
                (∀ z ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
                  a0 * ‖v‖ ^ 2 ≤ g.pullbackCoefficients Φ z v v ∧
                    g.pullbackCoefficients Φ z v v ≤ b0 * ‖v‖ ^ 2) ∧
                (∀ z ∈ Metric.closedBall 0 ρ, ∀ n ≤ m,
                  ‖iteratedFDeriv ℝ n (g.pullbackCoefficients Φ) z‖ ≤ Z) := by
  let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
  let qU : U := ⟨q, hq⟩
  obtain ⟨R, hR, Φ, hsource, hzero, hmap, hbuffer⟩ :=
    limitFinite_exists_original_chart U qU
  let ρ := R / 4
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρR : 2 * ρ < R := by dsimp only [ρ]; linarith
  let native := extChartAt (𝓡 3) q
  let z0 : E := native q
  let K : Set E := (fun z : E => z0 + z) '' Metric.closedBall 0 (2 * ρ)
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : E) (2 * ρ)).image (continuous_const.add continuous_id)
  have hKt : K ⊆ native.target := by
    rintro y ⟨z, hz, rfl⟩
    exact (hbuffer z (Metric.closedBall_subset_closedBall hρR.le hz)).1
  have htarget (z : E) (hz : z ∈ Metric.ball 0 R) : z0 + z ∈ native.target :=
    (hbuffer z (Metric.ball_subset_closedBall hz)).1
  have hconv := limitCanonical_round_bilinear_coefficient_convergence P G q c hc
  let B := fun k y => ContinuousLinearMap.piLpBilinearFromCoordinates
    (p := 2) (q := 2) (𝕜 := ℝ)
    (fun a b : Fin 3 => blowupPullbackCoefficient (G.embedding k) q a b (c, y))
  have hpos : ∀ y ∈ K, ∀ v : E, v ≠ 0 →
      0 < (G.limit.flow.metric c).pullbackCoefficients native.symm y v v := by
    intro y hy v hv
    have hi : (mfderiv (𝓡 3) (𝓡 3) native.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) (x := q) (hKt hy))
    have hv' : mfderiv (𝓡 3) (𝓡 3) native.symm y v ≠ 0 := by
      intro h
      apply hv
      apply hi.injective
      simpa only [map_zero] using h
    exact (G.limit.flow.metric c).pos _ _ hv'
  obtain ⟨a0, ha0, b0, hb0, hquad⟩ :=
    terminalCurvature_eventually_compact_coefficient_bounds
      (isOpen_extChartAt_target q) hK hKt hconv.smooth hpos 0
      (fun n _ => hconv.jets n K hK hKt)
  refine ⟨R, ρ, hρ, hρR, Φ, hsource, hzero, hmap, a0, b0, ha0,
    zero_le_one.trans hb0, ?_⟩
  intro m
  obtain ⟨_a, _ha, Z, hZ, hjets⟩ :=
    terminalCurvature_eventually_compact_coefficient_bounds
      (isOpen_extChartAt_target q) hK hKt hconv.smooth hpos m
      (fun n _ => hconv.jets n K hK hKt)
  refine ⟨Z, hZ, ?_⟩
  filter_upwards [hquad, hjets, eventually_ge_atTop j,
    G.exhaustion.time_cofinal {c} isCompact_singleton (singleton_subset_iff.mpr hc)]
    with k hqk hjk hjk' htime
  have ht := htime (mem_singleton c)
  have hspace : G.exhaustion.space j ⊆ G.exhaustion.space k :=
    G.exhaustion.space_increasing hjk'
  refine ⟨ht, hspace, ?_⟩
  intro g hmetric
  have hcoeff (z : E) (hz : z ∈ Metric.ball 0 R) :
      g.pullbackCoefficients Φ z = B k (z0 + z) :=
    limitFinite_anchor_coefficients (L := G.limit) (G.embedding k)
      (G.exhaustion.space_open k) U qU hspace c ht g hmetric Φ hsource hmap hz (htarget z hz)
  constructor
  · intro z hz v
    have hzR : z ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hρR hz
    have hzK : z0 + z ∈ K := mem_image_of_mem _ hz
    rw [hcoeff z hzR]
    refine ⟨(hqk _ hzK).2.2 v, ?_⟩
    have hnorm : ‖B k (z0 + z)‖ ≤ b0 := by
      have h := (hqk _ hzK).2.1 0 le_rfl
      rw [norm_iteratedFDeriv_zero] at h
      exact h
    calc
      B k (z0 + z) v v ≤ ‖B k (z0 + z) v v‖ := le_abs_self _
      _ ≤ ‖B k (z0 + z) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖B k (z0 + z)‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (b0 * ‖v‖) * ‖v‖ := by gcongr
      _ = b0 * ‖v‖ ^ 2 := by ring
  · intro z hz n hn
    have hz2 : z ∈ Metric.closedBall 0 (2 * ρ) :=
      Metric.closedBall_subset_closedBall (by linarith) hz
    have hzR : z ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hρR hz2
    rw [limitFinite_anchor_coefficient_jets (L := G.limit) (G.embedding k)
      (G.exhaustion.space_open k) U qU hspace c ht g hmetric Φ hsource hmap htarget n hzR]
    exact (hjk _ (mem_image_of_mem _ hz2)).2.1 n hn

end PoincareConjecture.M47
