import PoincareConjecture.Definitions.M67
import PoincareConjecture.Proofs.M59.Providers
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Comparison.Transport.ThirdHomotopy

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology unitInterval

universe u

namespace PoincareConjecture











theorem m67_rebased_alpha_nonzero
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
    (x : M) (z : N)
    (piTwoM : Subsingleton (HomotopyGroup.Pi 2 M x))
    (piTwoN : Subsingleton (HomotopyGroup.Pi 2 N z))
    (f : ContinuousMap M N)
    (smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (L : M59LoopPostcomposition f)
    (p : Path (f x) z)
    (lp : M59ConstantLoopPath p)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop x))
    (beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N))
      (constantC1Loop z))
    (halpha : (S.core compactM connectedM x piTwoM).pi_two_pi_three alpha ≠ 1)
    (hbij : Function.Bijective
      (surgeryHomotopyMap (n := 3) f (rfl : f x = f x)))
    (hbeta : M59HigherBasepointTransport.map (B.transport 2) lp.loop
        (surgeryHomotopyMap (n := 2) L.map
          (L.map_based (rfl : f x = f x)) alpha) = beta) :
    (S.core compactN connectedN z piTwoN).pi_two_pi_three beta ≠ 1 := by
  let piTwoFx : Subsingleton (HomotopyGroup.Pi 2 N (f x)) :=
    ⟨fun a b => by
      apply (m59BasepointTransport_bijective (B.transport 2) p).1
      exact piTwoN.elim _ _⟩
  letI : Subsingleton (HomotopyGroup.Pi 2 N (f x)) := piTwoFx
  let CM := S.core compactM connectedM x piTwoM
  let CN := S.core compactN connectedN (f x) piTwoFx
  let CNz := S.core compactN connectedN z piTwoN
  have hα : alpha ≠ 1 := by
    intro h
    apply halpha
    rw [h]
    exact CM.pi_two_pi_three.map_one
  have hmap_one : surgeryHomotopyMap (n := 3) f (rfl : f x = f x)
      (1 : HomotopyGroup.Pi 3 M x) = 1 := by
    rw [SurgeryComparison.Topology.surgeryHomotopyMap_eq_postcomp 2 f x]
    exact (Poincare.Topology.homotopyGroupPostcomp 2 f x).map_one
  have hmap_one' : surgeryHomotopyMap (n := 3) f (rfl : f x = f x)
      (CM.pi_two_pi_three 1) = 1 := by
    rw [CM.pi_two_pi_three.map_one]
    exact hmap_one
  have himage : surgeryHomotopyMap (n := 2) L.map
      (L.map_based (rfl : f x = f x)) alpha ≠ 1 := by
    intro h
    have htarget : CN.pi_two_pi_three
        (surgeryHomotopyMap (n := 2) L.map
          (L.map_based (rfl : f x = f x)) alpha) = 1 := by
      rw [h]
      exact CN.pi_two_pi_three.map_one
    have hnat := S.naturality compactM connectedM compactN connectedN x (f x)
      piTwoM piTwoFx f smooth (rfl : f x = f x) L alpha
    have hzero : surgeryHomotopyMap (n := 3) f (rfl : f x = f x)
        (CM.pi_two_pi_three alpha) = 1 := by
      rw [← hnat]
      exact htarget
    apply hα
    apply CM.pi_two_pi_three.injective
    apply hbij.1
    exact hzero.trans hmap_one'.symm
  have hrebased : beta ≠ 1 := by
    intro h
    apply m59BasepointTransport_nonzero (B.transport 2) lp.loop himage
    rw [hbeta, h]
  intro h
  apply hrebased
  apply CNz.pi_two_pi_three.injective
  rw [h]
  exact CNz.pi_two_pi_three.map_one.symm

end PoincareConjecture
