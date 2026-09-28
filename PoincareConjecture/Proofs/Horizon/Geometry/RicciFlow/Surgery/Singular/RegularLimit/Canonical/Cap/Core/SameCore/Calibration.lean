import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.SameCore.TerminalBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Volume.Lower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem eventually_same_core_calibrated_volume
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
      ∀ N : CapCertificate (F.metric t),
        N.epsilon ≤ min CapCertificate.coreBallClearanceThreshold.{u}
          CapCertificate.sameCoreBallClearanceThreshold.{u} →
        N.cap_constant ≤ H.constant → N.connection = F.connection t →
        H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
        H.reference.forward t ht x₀ ∈ N.core →
        ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
        ∀ b : ℝ, -N.epsilon⁻¹ + 40 ≤ b →
          ∃ r : ℝ, 0 < r ∧
            scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04)
              ((H.terminalMetric P04).ball x r) = r⁻¹ ^ 2 ∧
            closure ((H.terminalMetric P04).ball x r) ⊆ H.regularReferencePreimage P04 t ht
              (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b) ∧
            IsCompact (closure ((H.terminalMetric P04).ball x r)) ∧
            ENNReal.ofReal ((3 / (4 * H.constant)) * r ^ 3) ≤
              calibratedMetricVolume (H.terminalMetric P04) ((H.terminalMetric P04).ball x r) := by
  let m := (H.terminalConnection P04).scalarCurvature x₀ / 2
  have hm : 0 < m := half_pos hx₀
  let L := H.constant / m + 1
  have hL : 0 < L := by dsimp [L]; positivity [H.constant_pos]
  have hscale : H.constant ≤ m * L ^ 2 := by
    have hcancel : m * (H.constant / m) = H.constant := mul_div_cancel₀ _ hm.ne'
    have hnonneg := mul_nonneg hm.le (sq_nonneg (H.constant / m))
    dsimp only [L]
    nlinarith [H.constant_pos]
  obtain ⟨cmax, hcmax, hvolume⟩ :=
    H.exists_eventually_captured_cap_terminal_core_volume_lower P04 hA x₀ hx₀
  obtain ⟨c₁, hc₁, hc₁max, hcontain⟩ :=
    H.exists_eventually_same_core_terminal_ball_containment P04 hA x₀ hx₀ L hcmax
  obtain ⟨c, hc, hcc₁, hcalibrate⟩ :=
    H.exists_eventually_cap_core_radius_persistence P04 hA x₀ hx₀ hc₁
  have hbase : ∀ᶠ t in 𝓝[<] T, m < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Ioi_mem_nhds (half_lt_self hx₀))
  filter_upwards [hbase, hcontain, hcalibrate, hvolume c hc (hcc₁.trans hc₁max)]
    with t hbase hcontain hcalibrate hvolume
  intro ht N hε hconstant hconnection hcapture hx₀core x hxcore b hb
  have hbase' : m ≤ N.connection.scalarCurvature (H.reference.forward t ht x₀) := by
    rw [hconnection, H.reference.scalar_pullback]
    exact hbase.le
  have hrL := (N.core_radius_lt_of_scalar_lower hconstant hm hL hscale
    (N.core_subset_carrier hx₀core) hbase' hxcore).le
  have hinside := hcontain ht N (hε.trans (min_le_right _ _))
    hconstant hconnection hcapture hx₀core x hxcore hrL b hb
  obtain ⟨r, hr, hrlo, hrhi, hcal, hcompact⟩ :=
    hcalibrate ht N hconstant hconnection hcapture hx₀core x hxcore
  refine ⟨r, hr, hcal, ?_, hcompact, ?_⟩
  · apply Subset.trans (closure_mono ?_) hinside
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (hrhi.trans
      (mul_le_mul_of_nonneg_right hcc₁.le (N.core_radius_pos _ hxcore).le)))
  · exact hvolume ht N (hε.trans (min_le_left _ _))
      hconstant hconnection hcapture hx₀core x hxcore r hrlo hrhi

end PoincareConjecture.SingularTimeAssumptions
