import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.SameCore.OldBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.TerminalBalls



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



theorem exists_eventually_same_core_terminal_ball_containment
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀)
    (L : ℝ) {cmax : ℝ} (hcmax : 1 < cmax) :
    ∃ c : ℝ, 1 < c ∧ c < cmax ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
          N.epsilon ≤ CapCertificate.sameCoreBallClearanceThreshold.{u} →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
            N.core_radius (H.reference.forward t ht x) ≤ L →
          ∀ b : ℝ, -N.epsilon⁻¹ + 40 ≤ b →
            closure ((H.terminalMetric P04).ball x
              (c * N.core_radius (H.reference.forward t ht x))) ⊆
                H.regularReferencePreimage P04 t ht
                  (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b) := by
  obtain ⟨δ, hδ, henlarge⟩ := H.exists_eventually_same_core_enlarged_old_balls P04 hA x₀ hx₀
  have hcont : ContinuousAt (fun c : ℝ => (c ^ 2 - 1) * L) 1 := by fun_prop
  have hsmall : ∀ᶠ c : ℝ in 𝓝 1, (c ^ 2 - 1) * L < δ :=
    hcont.eventually (Iio_mem_nhds (by simpa using hδ))
  have hchoose : ∀ᶠ c : ℝ in 𝓝[>] 1,
      1 < c ∧ c < cmax ∧ (c ^ 2 - 1) * L < δ := by
    have hmax : ∀ᶠ c : ℝ in 𝓝[>] 1, c < cmax :=
      nhdsWithin_le_nhds (Iio_mem_nhds hcmax)
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
      hmax] with c hc hs hmax'
    exact ⟨hc, hmax', hs⟩
  obtain ⟨c, hc, hcmax', hmargin⟩ := hchoose.exists
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hfactor : 0 ≤ c ^ 2 - 1 := by nlinarith
  refine ⟨c, hc, hcmax', ?_⟩
  filter_upwards [henlarge, H.eventually_terminal_tangentNorm_comparison P04 hA hc]
    with t henlarge hnorm
  intro ht N hε hconstant hconnection hcapture hx₀core x hxcore hrL b hb
  let p := H.reference.forward t ht x
  let r := N.core_radius p
  have hr : 0 < r := N.core_radius_pos p hxcore
  obtain ⟨hclosed, _⟩ := henlarge ht N hε hconstant hconnection hcapture hx₀core p
    (N.core_subset_closed_core hxcore) r hr
    (fun _ hy => N.core_ball_subset p hxcore (subset_closure hy)) (N.core_radius_eq p hxcore) b hb
  have hcomparison : c * (c * r) ≤ r + δ := by
    have hm := (mul_le_mul_of_nonneg_left hrL hfactor).trans_lt hmargin
    change (c ^ 2 - 1) * r < δ at hm
    nlinarith
  have hsub : N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b ⊆ N.carrier :=
    union_subset N.closed_core_subset_carrier
      ((N.end_neck.region_subset_carrier _ _).trans N.end_neck_subset)
  exact (H.terminal_closedBall_subset_of_captured_old_ball P04 hA t ht x (add_pos hr hδ)
    hcpos hcomparison _ ((image_mono hsub).trans hcapture) hclosed
    (fun y hy v => (hnorm y hy v).2)).1

end PoincareConjecture.SingularTimeAssumptions
