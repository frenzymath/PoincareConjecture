import PoincareConjecture.Proofs.M38.EventSlices

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

theorem canonical_region
    (N : RepairedNeckCapTopologyTheory.{u}) (F : SurgeryFlowData.{u}) (t : ℝ)
    {X : Set (F.slice t).carrier} (hX : IsConnected X)
    (hcontrol : ∀ x ∈ X,
      SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (hepsilon : F.parameters.epsilon ≤ N.epsilon₀) :
    (∃ H : ConnectedNeckCapCover (F.metric t),
      H.X = X ∧ H.epsilon = F.parameters.epsilon ∧
      H.epsilon_threshold = N.epsilon₀ ∧ H.cap_constant = F.parameters.C ∧
      Nonempty (RepairedNeckCapTopologyData (F.metric t) H)) ∨
    (∃ Q : SingularCComponent (F.metric t) (F.connection t) F.parameters.C,
      X ⊆ Q.carrier) ∨
    (∃ Q : SingularRoundComponent (F.metric t) F.parameters.epsilon,
      X ⊆ Q.carrier) := by
  classical
  by_cases hcomponent : ∃ Q :
      SingularCComponent (F.metric t) (F.connection t) F.parameters.C,
      X ⊆ Q.carrier
  · exact Or.inr (Or.inl hcomponent)
  by_cases hround : ∃ Q : SingularRoundComponent (F.metric t) F.parameters.epsilon,
      X ⊆ Q.carrier
  · exact Or.inr (Or.inr hround)
  left
  let H : ConnectedNeckCapCover (F.metric t) :=
    { epsilon := F.parameters.epsilon
      epsilon_pos := F.parameters.epsilon_pos
      epsilon_threshold := N.epsilon₀
      epsilon_threshold_pos := N.epsilon₀_pos
      epsilon_threshold_le_one_two_hundred := N.epsilon₀_le_one_two_hundred
      epsilon_le_threshold := hepsilon
      cap_constant := F.parameters.C
      cap_constant_pos := F.parameters.C_pos
      X := X
      connected_X := hX
      necks := {K | K.epsilon = F.parameters.epsilon}
      caps := {K | K.epsilon = F.parameters.epsilon ∧ K.cap_constant ≤ F.parameters.C}
      pointwise_cover := by
        intro x hx
        cases hcontrol x hx with
        | neck K hcenter =>
          exact Or.inl ⟨K.neck, K.epsilon_eq, hcenter⟩
        | cap K he hc _ hcore =>
          exact Or.inr ⟨K, ⟨he, hc⟩, hcore⟩
        | component Q hmem =>
          apply (hcomponent ?_).elim
          refine ⟨Q, ?_⟩
          rw [Q.component_eq] at hmem ⊢
          rw [connectedComponent_eq hmem]
          exact hX.subset_connectedComponent hx
        | round Q hmem =>
          apply (hround ?_).elim
          refine ⟨Q, ?_⟩
          rw [Q.component_eq] at hmem ⊢
          rw [connectedComponent_eq hmem]
          exact hX.subset_connectedComponent hx
      neck_epsilon := fun _ hK => hK
      cap_epsilon := fun _ hK => hK.1
      cap_constant_bound := fun _ hK => hK.2 }
  exact ⟨H, rfl, rfl, rfl, rfl, N.a21 (F.metric t) H hepsilon⟩

def roundSpaceform {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {epsilon : ℝ}
    (Q : SingularRoundComponent g epsilon) : SurgeryPositiveSpaceform Q.model where
  metric := Q.model_metric
  connection := Q.model_connection
  compact := Q.model_compact
  connected := Q.model_connected
  round := ⟨1, zero_lt_one, fun x v w hv hw hvw =>
    Q.model_curvature_one x v w ⟨hv, hw, hvw⟩⟩

end PoincareConjecture.M38
