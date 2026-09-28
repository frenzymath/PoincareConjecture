import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.EventClassRebase
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Groups.HomotopyGroupHomeomorph
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.LoopSpace.Evaluation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology unitInterval

universe u

namespace PoincareConjecture

noncomputable def m67ConstantLoopPath
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {x y : M} (p : Path x y) :
    M59ConstantLoopPath p where
  loop := p.map LoopSpace.continuous_constantC1Loop
  pointwise := fun _ _ => rfl

theorem m67_pi_two_trivial_of_homeomorph
    (B : M59HigherBasepointTransportService.{u})
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (x : M) (y : N) (p : Path (e x) y)
    (h : Subsingleton (HomotopyGroup.Pi 2 M x)) :
    Subsingleton (HomotopyGroup.Pi 2 N y) := by
  have hf := (Poincare.Topology.homotopyGroupPostcomp_homeomorph_bijective 1 e x).2
  have hp := (m59BasepointTransport_bijective (B.transport 2) p).2
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hp a
  obtain ⟨b', rfl⟩ := hp b
  obtain ⟨a'', rfl⟩ := hf a'
  obtain ⟨b'', rfl⟩ := hf b'
  rw [h.elim a'' b'']



theorem m67_alpha_transport_of_diffeomorph
    (S : M59IdentificationSystem.{u})
    (B : M59HigherBasepointTransportService.{u})
    {M N : Type u}
    [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace LoopAmbient N]
    [IsManifold (𝓡 3) ∞ N]
    [T2Space N] [SecondCountableTopology N]
    (compactM : IsCompact (Set.univ : Set M))
    (connectedM : IsConnected (Set.univ : Set M))
    (compactN : IsCompact (Set.univ : Set N))
    (connectedN : IsConnected (Set.univ : Set N))
    (x : M) (y : N)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (p : Path (e x) y) (lp : M59ConstantLoopPath p)
    (piTwoM : Subsingleton (HomotopyGroup.Pi 2 M x))
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (halpha : (S.core compactM connectedM x piTwoM).pi_two_pi_three alpha ≠ 1) :
    ∃ piTwoN : Subsingleton (HomotopyGroup.Pi 2 N y),
      ∃ beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N)) (constantC1Loop y),
        (S.core compactN connectedN y piTwoN).pi_two_pi_three beta ≠ 1 ∧
        M67AlphaTransport B x y (e.toHomeomorph : C(M, N)) alpha beta := by
  let f : C(M, N) := e.toHomeomorph
  obtain ⟨L⟩ := S.postcomposition f e.contMDiff
  let piTwoN := m67_pi_two_trivial_of_homeomorph B e.toHomeomorph x y p piTwoM
  let beta := M59HigherBasepointTransport.map (B.transport 2) lp.loop
    (surgeryHomotopyMap (n := 2) L.map (L.map_based (rfl : f x = f x)) alpha)
  refine ⟨piTwoN, beta, ?_, L, p, lp, rfl⟩
  apply m67_rebased_alpha_nonzero S B compactM connectedM compactN connectedN
    x y piTwoM piTwoN f e.contMDiff L p lp alpha beta halpha
  · exact Poincare.Topology.homotopyGroupPostcomp_homeomorph_bijective 2
      e.toHomeomorph x
  · rfl

end PoincareConjecture
