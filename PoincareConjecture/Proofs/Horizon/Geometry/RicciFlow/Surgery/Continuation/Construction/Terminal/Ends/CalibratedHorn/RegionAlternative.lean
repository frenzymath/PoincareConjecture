import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeHorn
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.WeakFrontier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Regions









noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_calibrated_strongHorn_or_capped_region (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u}) (hA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀)
    (hconstant : 2 ≤ H.constant)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x ≤ rho⁻¹ ^ 2) :
    (∃ horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon),
      horn.carrier ⊆ K.component ∧
      (∃ n : ℕ, Subtype.val '' e.tail n ⊆ horn.carrier) ∧
      Disjoint horn.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} ∧
      (∀ x ∈ horn.boundary_sphere, Q.terminal_scalar x < 8 * H.constant * rho⁻¹ ^ 2) ∧
      HornBoundaryBelow horn (rho / (2 * H.constant))) ∨
    ∃ (n : ℕ) (X : Set (Q.extension.extended.slice T).carrier)
      (Y : CappedTubeCertificate (Q.extension.extended.metric T)),
      IsClosed X ∧ IsConnected X ∧ X ⊆ K.component ∧
      Subtype.val '' e.tail n ⊆ X ∧ ¬ IsCompact X ∧
      (∀ x ∈ X, rho⁻¹ ^ 2 ≤ Q.terminal_scalar x) ∧
      (∃ x ∈ X, Q.terminal_scalar x = rho⁻¹ ^ 2) ∧
      IsCompact (frontier X) ∧
      (∀ x ∈ frontier X, Q.terminal_scalar x = rho⁻¹ ^ 2) ∧
      X ⊆ Y.carrier ∧ Y.cap.epsilon = terminalAccuracyFactor * H.epsilon ∧
      Y.tube.epsilon = terminalAccuracyFactor * H.epsilon ∧ Y.cap.cap_constant ≤ 2 * H.constant ∧
      (X ∩ Y.cap.carrier).Nonempty := by
  have hq : H.r₀⁻¹ ^ 2 < rho⁻¹ ^ 2 := by
    have hinv := (inv_lt_inv₀ H.r₀_pos hrho).mpr hrho_r₀
    nlinarith [inv_pos.mpr H.r₀_pos, inv_pos.mpr hrho]
  obtain ⟨n, X, hclosed, hconnected, hcomponent, htail, hnoncompact,
    hbound, hattain, hfrontcompact, hfront⟩ :=
    Q.exists_end_region_of_low_point K e (rho⁻¹ ^ 2) hlow
  let C := Q.endRegionCover A hA K e X hconnected hcomponent
    (fun x hx => hq.trans_le (hbound x hx))
  obtain ⟨R⟩ := A.a21 (Q.extension.extended.metric T) C hA
  rcases Q.tube_or_cappedTube_of_noncompact C R hclosed hnoncompact with
    ⟨tube, _⟩ | ⟨Y, hXY, hcapε, htubeε, hcapC⟩
  · exact Or.inl (Q.exists_calibrated_strongHorn_of_tube_region A hA K e X tube
      rho hrho hrho_r₀ hconstant hclosed hcomponent hfront n htail hlow)
  · by_cases hmeet : (X ∩ Y.cap.carrier).Nonempty
    · exact Or.inr ⟨n, X, Y, hclosed, hconnected, hcomponent, htail, hnoncompact,
        hbound, hattain, hfrontcompact, hfront, hXY, hcapε, htubeε, hcapC, hmeet⟩
    · have hXtube : X ⊆ Y.tube.carrier := by
        intro x hx
        have hy := hXY hx
        rw [Y.carrier_eq_union] at hy
        exact hy.resolve_left (fun hcap => hmeet ⟨x, hx, hcap⟩)
      let tube : EpsilonTubeCertificate (Q.extension.extended.metric T) X :=
        { Y.tube with contains_X := hXtube }
      exact Or.inl (Q.exists_calibrated_strongHorn_of_tube_region A hA K e X tube
        rho hrho hrho_r₀ hconstant hclosed hcomponent hfront n htail hlow)

end PoincareConjecture.SingularLimitConclusion
