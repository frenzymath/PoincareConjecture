import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.ClosedHalf
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.ProperEnds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.WeakFrontier


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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



theorem exists_closed_cylinder_half_at_cappedTube_neck (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    {X : Set (Q.extension.extended.slice T).carrier}
    (hX : IsClosed X) (hfront : IsCompact (frontier X)) (hXY : X ⊆ Y.carrier)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X)
    (N : EpsilonNeck (Q.extension.extended.metric T))
    (hepsilon : N.epsilon ≤ 1 / 200) (hNU : N.carrier ⊆ Y.tube.carrier) :
    ∃ (P : OpenCylinderModel Y.tube.carrier) (side : Bool),
      P.middleSphere = N.central_sphere ∧ IsClosed (P.closedTail side (1 / 2)) ∧
      ∃ k : ℕ, Subtype.val '' e.tail k ⊆ P.closedTail side (1 / 2) := by
  have hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((Q.extension.extended.connection T).scalarCurvature ⁻¹' D) := by
    simpa only [Q.terminal_scalar_eq] using Q.scalar_proper
  let Z := X \ Y.cap.carrier
  have hZclosed : IsClosed Z := hX.inter Y.cap.carrier_open.isClosed_compl
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
  have hZtail : Subtype.val '' e.tail (max n m) ⊆ Z := by
    intro x hx
    exact ⟨htail (image_mono (e.nested (le_max_left n m)) hx),
      fun hcap => disjoint_left.mp (hm (max n m) (le_max_right n m)) hx hcap⟩
  exact e.exists_closed_cylinder_half_at_neck tube hZclosed hZfront
    (max n m) hZtail N hepsilon hNU



theorem exists_end_region_in_tube_of_low_neck (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    {X : Set (Q.extension.extended.slice T).carrier}
    (hX : IsClosed X) (hfront : IsCompact (frontier X)) (hXY : X ⊆ Y.carrier)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X)
    (N : EpsilonNeck (Q.extension.extended.metric T))
    (hepsilon : N.epsilon ≤ 1 / 200) (hNU : N.carrier ⊆ Y.tube.carrier)
    (q : ℝ) (hq : 0 < q)
    (hNlow : ∀ x ∈ N.central_sphere, Q.terminal_scalar x < 2 * q)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x ≤ q) :
    ∃ (k : ℕ) (Z : Set (Q.extension.extended.slice T).carrier),
      IsClosed Z ∧ IsConnected Z ∧ Z ⊆ K.component ∧
      Subtype.val '' e.tail k ⊆ Z ∧ ¬ IsCompact Z ∧
      (∀ x ∈ Z, 4 * q ≤ Q.terminal_scalar x) ∧
      (∃ x ∈ Z, Q.terminal_scalar x = 4 * q) ∧ IsCompact (frontier Z) ∧
      (∀ x ∈ frontier Z, Q.terminal_scalar x = 4 * q) ∧ Z ⊆ Y.tube.carrier := by
  obtain ⟨P, side, hP, hclosed, m, hm⟩ :=
    Q.exists_closed_cylinder_half_at_cappedTube_neck K e Y hX hfront hXY n htail
      N hepsilon hNU
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hboundary : ∀ x ∈ frontier (P.closedTail side (1 / 2)),
      Q.terminal_scalar x < 2 * q := by
    intro x hx
    apply hNlow x
    rw [← hP]
    exact P.frontier_closedTail_subset_axialSphere Y.tube.carrier_open side hhalf hclosed hx
  have hlow' : ∃ x ∈ K.component, Q.terminal_scalar x ≤ 4 * q := by
    obtain ⟨x, hx, h⟩ := hlow
    exact ⟨x, hx, h.trans (by linarith)⟩
  obtain ⟨k, Z, hZclosed, hZconn, hZK, hZtail, hZnoncompact, hZhigh,
    hZattain, hZfront, hZlevel⟩ := Q.exists_end_region_of_low_point K e (4 * q) hlow'
  have hdis : Disjoint Z (frontier (P.closedTail side (1 / 2))) := by
    apply disjoint_left.mpr
    intro x hx hxfront
    have h1 := hZhigh x hx
    have h2 := hboundary x hxfront
    linarith
  have hZhalf : Z ⊆ interior (P.closedTail side (1 / 2)) := by
    apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      hZconn.isPreconnected hdis
    obtain ⟨x, hx⟩ := (e.tail_image_connected (max k m)).nonempty
    have hxZ := hZtail (image_mono (e.nested (le_max_left k m)) hx)
    have hxS := hm (image_mono (e.nested (le_max_right k m)) hx)
    refine ⟨x, hxZ, ?_⟩
    by_contra hout
    exact disjoint_left.mp hdis hxZ ⟨subset_closure hxS, hout⟩
  refine ⟨k, Z, hZclosed, hZconn, hZK, hZtail, hZnoncompact, hZhigh,
    hZattain, hZfront, hZlevel, ?_⟩
  intro x hx
  exact ((P.mem_closedTail_iff side hhalf).mp (interior_subset (hZhalf hx))).1

end PoincareConjecture.SingularLimitConclusion
