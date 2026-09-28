import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Superlevel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Theory

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

theorem neck_or_cap_on_end_component (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    {x : (Q.extension.extended.slice T).carrier} (hx : x ∈ K.component)
    (hscalar : H.r₀⁻¹ ^ 2 < Q.terminal_scalar x) :
    (∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x) ∨
      ∃ cap : CapCertificate (Q.extension.extended.metric T),
        cap.epsilon = terminalAccuracyFactor * H.epsilon ∧ cap.cap_constant ≤ 2 * H.constant ∧
        cap.connection = Q.extension.extended.connection T ∧ x ∈ cap.core := by
  have hnoncompact := e.not_isCompact_component
  have hK : connectedComponent x = K.component := by
    rw [K.component_eq] at hx ⊢
    exact (connectedComponent_eq hx).symm
  cases Q.canonical_neighborhood x hscalar with
  | neck N hcenter => exact Or.inl ⟨N, hcenter⟩
  | cap N hepsilon hconstant hconnection hcore =>
      exact Or.inr ⟨N, hepsilon, hconstant, hconnection, hcore⟩
  | component N hcontains =>
      have hN : connectedComponent x = N.carrier := by
        rw [N.component_eq] at hcontains ⊢
        exact (connectedComponent_eq hcontains).symm
      exact (hnoncompact (hN.symm.trans hK ▸ N.compact)).elim
  | round N hcontains =>
      have hN : connectedComponent x = N.carrier := by
        rw [N.component_eq] at hcontains ⊢
        exact (connectedComponent_eq hcontains).symm
      exact (hnoncompact (hN.symm.trans hK ▸ N.compact)).elim

def endRegionCover (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u})
    (haccuracy : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier) (hX : IsConnected X)
    (hcomponent : X ⊆ K.component)
    (hscalar : ∀ x ∈ X, H.r₀⁻¹ ^ 2 < Q.terminal_scalar x) :
    ConnectedNeckCapCover (Q.extension.extended.metric T) := by
  have hepsilon : terminalAccuracyFactor * H.epsilon < 1 / 2 := by
    linarith [A.epsilon₀_le_one_two_hundred]
  refine {
    epsilon := terminalAccuracyFactor * H.epsilon
    epsilon_pos := mul_pos terminalAccuracyFactor_pos H.epsilon_pos
    epsilon_threshold := A.epsilon₀
    epsilon_threshold_pos := A.epsilon₀_pos
    epsilon_threshold_le_one_two_hundred := A.epsilon₀_le_one_two_hundred
    epsilon_le_threshold := haccuracy
    cap_constant := 2 * H.constant
    cap_constant_pos := mul_pos (by norm_num) H.constant_pos
    X := X
    connected_X := hX
    necks := {N | ∃ S : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon),
      N = S.spatialNeck hepsilon ∧ S.center ∈ X}
    caps := {cap | cap.epsilon = terminalAccuracyFactor * H.epsilon ∧
      cap.cap_constant ≤ 2 * H.constant ∧
      cap.connection = Q.extension.extended.connection T ∧ (cap.core ∩ X).Nonempty}
    pointwise_cover := ?_
    neck_epsilon := ?_
    cap_epsilon := ?_
    cap_constant_bound := ?_ }
  · intro x hx
    rcases Q.neck_or_cap_on_end_component K e (hcomponent hx) (hscalar x hx) with
      ⟨N, hcenter⟩ | ⟨cap, heps, hconst, hconn, hcore⟩
    · exact Or.inl ⟨N.spatialNeck hepsilon, ⟨N, rfl, hcenter ▸ hx⟩, hcenter⟩
    · exact Or.inr ⟨cap, ⟨heps, hconst, hconn, x, hcore, hx⟩, hcore⟩
  · rintro N ⟨S, rfl, hS⟩
    rfl
  · exact fun cap hcap => hcap.1
  · exact fun cap hcap => hcap.2.1

@[simp] theorem endRegionCover_X (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u})
    (haccuracy : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier) (hX : IsConnected X)
    (hcomponent : X ⊆ K.component)
    (hscalar : ∀ x ∈ X, H.r₀⁻¹ ^ 2 < Q.terminal_scalar x) :
    (Q.endRegionCover A haccuracy K e X hX hcomponent hscalar).X = X := rfl

end PoincareConjecture.SingularLimitConclusion
