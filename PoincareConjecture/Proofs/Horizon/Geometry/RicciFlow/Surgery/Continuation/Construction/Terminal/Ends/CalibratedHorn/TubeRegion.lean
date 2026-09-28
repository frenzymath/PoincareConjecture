import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Frontier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeStrongCenters








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

theorem exists_strong_end_region_in_tube (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier)
    (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) X)
    (q : ℝ) (hq : H.r₀⁻¹ ^ 2 < q) (hconstant : 1 ≤ H.constant)
    (hclosed : IsClosed X) (hcomponent : X ⊆ K.component)
    (hfront : ∀ x ∈ frontier X, Q.terminal_scalar x = q)
    (k : ℕ) (htail : Subtype.val '' e.tail k ⊆ X)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x < 4 * H.constant * q) :
    ∃ (n : ℕ) (Z : Set (Q.extension.extended.slice T).carrier),
      IsClosed Z ∧ IsConnected Z ∧ IsCompact (frontier Z) ∧
      Z ⊆ interior X ∧ Subtype.val '' e.tail n ⊆ Z ∧
      (∀ x ∈ Z, 4 * H.constant * q ≤ Q.terminal_scalar x) ∧
      (∃ x ∈ Z, Q.terminal_scalar x = 4 * H.constant * q) ∧
      (∀ x ∈ Z,
        ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x) ∧
      ∀ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center ∈ Z →
        N.carrier ⊆ interior X ∧ ∀ x ∈ N.carrier,
          ∃ P : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon),
            P.center = x := by
  obtain ⟨n, Z, hZclosed, hZconnected, _, hZtail, _, hZhigh, hattain, hZfront, _⟩ :=
    Q.exists_end_superlevel_region_compact_frontier K e (4 * H.constant * q) hlow
  have hqpos : 0 < q := lt_of_le_of_lt (sq_nonneg _) hq
  have hlevel : q < 4 * H.constant * q := by
    nlinarith [mul_le_mul_of_nonneg_right hconstant hqpos.le]
  have hdisjoint : Disjoint Z (frontier X) := by
    refine disjoint_left.mpr fun x hx hxf => ?_
    exact (hlevel.trans_le (hZhigh x hx)).ne' (hfront x hxf)
  have hZX : Z ⊆ interior X := by
    apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      hZconnected.isPreconnected hdisjoint
    obtain ⟨p, hp⟩ := (e.isConnected_tail (max n k)).nonempty
    have hpZ : p.val ∈ Z := hZtail ⟨p, e.nested (le_max_left _ _) hp, rfl⟩
    have hpX : p.val ∈ X := htail ⟨p, e.nested (le_max_right _ _) hp, rfl⟩
    refine ⟨p.val, hpZ, ?_⟩
    by_contra hni
    exact disjoint_left.mp hdisjoint hpZ ⟨subset_closure hpX, hni⟩
  refine ⟨n, Z, hZclosed, hZconnected, hZfront, hZX, hZtail, hZhigh, hattain, ?_, ?_⟩
  · intro x hx
    apply Q.strong_neck_center_of_tube_high_point K e X tube q hclosed hcomponent
      hfront (interior_subset (hZX hx)) (hq.trans (hlevel.trans_le (hZhigh x hx)))
    have hmul : 0 < H.constant * q := mul_pos H.constant_pos hqpos
    linarith [hZhigh x hx]
  · intro N hN
    exact Q.strong_neck_carrier_has_strong_centers_of_tube_high_center K e X tube q
      hq hconstant hclosed hcomponent hfront N (interior_subset (hZX hN)) (hZhigh _ hN)

end PoincareConjecture.SingularLimitConclusion
