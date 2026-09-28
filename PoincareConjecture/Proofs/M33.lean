import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.TerminalPolicy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.OldEventPolicy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.ContinuationPolicy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.MaximalRestart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.RestartPinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Predecessors
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Preservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Service
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Conclusion

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem repairedBranchContinuation
    (P : M33Predecessors.{u}) : RepairedBranchContinuationTheory.{u} := by
  classical
  refine ⟨P.regular_history, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T I G H L N bridge
  by_cases hempty : I.controlled_core = ∅
  · exact bridge.continuation_of_core_empty hempty
  · have hcore : I.controlled_core.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    by_cases hsmall : H.constant ≤ 99
    · exact bridge.continuation_of_constant_le_ninetyNine P hcore hsmall
    · apply bridge.continuation_of_calibrated_horns P hcore
      intro K hK e
      have hrho : I.rho < H.r₀ := bridge.parameter_r₀_eq.symm ▸ I.rho_lt_r₀
      have hconstant : 8 ≤ H.constant := by linarith
      have hlow : ∃ x ∈ K.component, N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2 := hK
      rcases N.limit.exists_calibrated_strongHorn_or_capped_region
        bridge.appendixA bridge.appendixA_accuracy K e I.rho I.rho_pos hrho
        (by linarith) hlow with hhorn | hcapped
      · obtain ⟨horn, hcomponent, htail, hdisjoint, hlinear, hboundary⟩ := hhorn
        refine ⟨horn, hboundary, ?_, hcomponent, ?_, htail⟩
        · intro x hx
          rw [← N.limit.terminal_scalar_eq]
          have hpos : 0 < H.constant * I.rho⁻¹ ^ 2 :=
            mul_pos H.constant_pos (sq_pos_of_pos (inv_pos.mpr I.rho_pos))
          nlinarith [hlinear x hx]
        · simpa only [N.limit.terminal_scalar_eq] using hdisjoint
      · obtain ⟨n, X, Y, hX, hconnected, hcomponent, htail, hnoncompact,
          hbound, hattain, hfront, hfrontlevel, hXY, hcapε, htubeε, hcapC, hmeet⟩ := hcapped
        have hproper : ∀ D : Set ℝ, IsCompact D →
            IsCompact ((N.limit.extension.extended.connection T).scalarCurvature ⁻¹' D) := by
          simpa only [N.limit.terminal_scalar_eq] using N.limit.scalar_proper
        have hY := e.cappedTube_carrier_eq_component hproper Y hX hfront hXY n htail
        by_cases htubelow : ∃ p ∈ Y.tube.carrier,
            N.limit.terminal_scalar p ≤ I.rho⁻¹ ^ 2
        · obtain ⟨p, hp, hplow⟩ := htubelow
          have hpK : p ∈ K.component := hY ▸ Y.tube_subset hp
          obtain ⟨horn, hhornK, hhornTail, hhornLow, hlinear, hboundary⟩ :=
            N.limit.exists_calibrated_strongHorn_of_cappedTube_low_tube_point
              bridge.appendixA bridge.appendixA_accuracy K e Y hX hfront hXY n htail
              I.rho I.rho_pos hrho hconstant hp hpK hplow
          refine ⟨horn, hboundary, ?_, hhornK, ?_, hhornTail⟩
          · simpa only [N.limit.terminal_scalar_eq] using hlinear
          · simpa only [N.limit.terminal_scalar_eq] using hhornLow
        · have htubehigh : ∀ x ∈ Y.tube.carrier,
              I.rho⁻¹ ^ 2 < N.limit.terminal_scalar x := by
            intro x hx
            exact lt_of_not_ge (fun h => htubelow ⟨x, hx, h⟩)
          obtain ⟨p, hpK, hplow⟩ := hlow
          have hpcap : p ∈ Y.cap.carrier := by
            have hpY : p ∈ Y.carrier := hY.symm ▸ hpK
            rw [Y.carrier_eq_union] at hpY
            exact hpY.resolve_right (fun hp => (htubehigh p hp).not_ge hplow)
          have hq : H.r₀⁻¹ ^ 2 < I.rho⁻¹ ^ 2 := by
            have hi := (inv_lt_inv₀ H.r₀_pos I.rho_pos).mpr hrho
            nlinarith [inv_pos.mpr H.r₀_pos, inv_pos.mpr I.rho_pos]
          have hstrong : ∀ x ∈ K.component,
              2 * H.constant * I.rho⁻¹ ^ 2 ≤ N.limit.terminal_scalar x →
              ∃ S : TerminalStrongNeck N.limit.extension (terminalAccuracyFactor * H.epsilon),
                S.center = x := by
            intro x hx hxhigh
            apply N.limit.strong_neck_center_of_cappedTube_high_point K e Y hY
              hcapε hcapC (I.rho⁻¹ ^ 2) hpcap hplow hx ?_ hxhigh
            have hqpos : 0 < I.rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr I.rho_pos)
            nlinarith [mul_le_mul_of_nonneg_right hconstant hqpos.le]
          obtain ⟨horn, hhornK, hhornTail, hhornLow, hlinear, hboundary⟩ :=
            N.limit.exists_calibrated_strongHorn_of_high_strong_centers
              bridge.appendixA bridge.appendixA_accuracy K e I.rho I.rho_pos
              (by linarith) hK hstrong
          refine ⟨horn, hboundary, ?_, hhornK, ?_, hhornTail⟩
          · intro x hx
            rw [← N.limit.terminal_scalar_eq]
            have hpos : 0 < H.constant * I.rho⁻¹ ^ 2 :=
              mul_pos H.constant_pos (sq_pos_of_pos (inv_pos.mpr I.rho_pos))
            nlinarith [hlinear x hx]
          · simpa only [N.limit.terminal_scalar_eq] using hhornLow

end PoincareConjecture
