import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeEnds
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

theorem exists_proper_tube_end_above (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u})
    (haccuracy : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (q : ℝ) (hq : H.r₀⁻¹ ^ 2 < q)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x < q) :
    ∃ (X : Set (Q.extension.extended.slice T).carrier)
      (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) X),
      tube.epsilon = terminalAccuracyFactor * H.epsilon ∧ IsClosed X ∧ IsCompact (frontier X) ∧
      X ⊆ K.component ∧ (∀ x ∈ X, q ≤ Q.terminal_scalar x) ∧
      ∃ (side : Bool) (a : ℝ) (k : ℕ), a ∈ Ioo (0 : ℝ) 1 ∧
        tube.cylinder.closedTail side a ⊆ X ∧
        IsClosed (tube.cylinder.closedTail side a) ∧
        IsProperMap (fun z : (univ ×ˢ if side then Ico a 1 else Ioc 0 a) =>
          tube.cylinder.coordinate z.val) ∧
        ∀ m : ℕ, k ≤ m → Subtype.val '' e.tail m ⊆ tube.cylinder.tail side a := by
  obtain ⟨n, X, hclosed, hconn, hcomponent, htail, hnoncompact, hbound,
    _, hfront, _⟩ := Q.exists_end_superlevel_region_compact_frontier K e q hlow
  let C := Q.endRegionCover A haccuracy K e X hconn hcomponent
    (fun x hx => hq.trans_le (hbound x hx))
  obtain ⟨R⟩ := A.a21 (Q.extension.extended.metric T) C haccuracy
  have hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((Q.extension.extended.connection T).scalarCurvature ⁻¹' D) := by
    simpa only [Q.terminal_scalar_eq] using Q.scalar_proper
  have hchoice : ∃ (Z : Set (Q.extension.extended.slice T).carrier)
      (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) Z),
      tube.epsilon = terminalAccuracyFactor * H.epsilon ∧ Z ⊆ X ∧ IsClosed Z ∧
      IsCompact (frontier Z) ∧ ∃ m : ℕ, Subtype.val '' e.tail m ⊆ Z := by
    rcases Q.tube_or_cappedTube_of_noncompact C R hclosed hnoncompact with
      ⟨tube, hepsilon⟩ | ⟨Y, hXY, _, hepsilon, _⟩
    · exact ⟨X, tube, hepsilon, Subset.rfl, hclosed, hfront, n, htail⟩
    · let Z := X \ Y.cap.carrier
      have hZclosed : IsClosed Z := hclosed.inter Y.cap.carrier_open.isClosed_compl
      have hZtube : Z ⊆ Y.tube.carrier := by
        intro x hx
        have hy := hXY hx.1
        rw [Y.carrier_eq_union] at hy
        exact hy.resolve_left hx.2
      have hcapcompact : IsCompact (frontier Y.cap.carrier) :=
        (Y.cap.isCompact_closure_of_scalar_proper (Q.extension.extended.connection T)
          hproper).of_isClosed_subset isClosed_frontier frontier_subset_closure
      have hZfront : IsCompact (frontier Z) := by
        apply (hfront.union hcapcompact).of_isClosed_subset isClosed_frontier
        intro x hx
        rcases frontier_inter_subset X Y.cap.carrierᶜ hx with hx | hx
        · exact Or.inl hx.1
        · exact Or.inr (by simpa only [frontier_compl] using hx.2)
      obtain ⟨m, hm⟩ := e.exists_tail_disjoint_cap hproper Y.cap
      let tube : EpsilonTubeCertificate (Q.extension.extended.metric T) Z :=
        { Y.tube with contains_X := hZtube }
      refine ⟨Z, tube, hepsilon, sdiff_subset, hZclosed, hZfront, max n m, ?_⟩
      intro x hx
      exact ⟨htail (image_mono (e.nested (le_max_left n m)) hx),
        fun hcap => disjoint_left.mp (hm (max n m) (le_max_right n m)) hx hcap⟩
  obtain ⟨Z, tube, hepsilon, hZX, hZclosed, hZfront, m, hm⟩ := hchoice
  obtain ⟨side, a, k, ha, _, hsub, hc, hp, hcarry⟩ :=
    e.exists_proper_closed_tube_tail hZclosed hZfront tube m hm
  exact ⟨Z, tube, hepsilon, hZclosed, hZfront, hZX.trans hcomponent,
    fun x hx => hbound x (hZX hx), side, a, k, ha, hsub, hc, hp, hcarry⟩

end PoincareConjecture.SingularLimitConclusion
