import PoincareConjecture.Statements.M59LoopClasses
import PoincareConjecture.Definitions.M59BasepointTransport
import PoincareConjecture.Proofs.M02
import PoincareConjecture.Proofs.M58










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareConjecture

theorem m59ClosedTopologyProvider_from_M02 : RepairedClosedTopologyProvider.{u} := by
  intro M _ _ _ _ _ _ _
  exact closedSimplyConnectedThreeManifoldTopology

theorem m59ComponentRepresentative_from_identification
    (S : M59IdentificationSystem.{u}) : M59ComponentRepresentativeClaim S := by
  intro A C pi_two_trivial xi
  obtain ⟨Gamma, hnormalized, hclass⟩ :=
    (S.core C.compact C.connected C.basepoint pi_two_trivial).regular_representatives
      ((S.core C.compact C.connected C.basepoint pi_two_trivial).pi_two_pi_three.symm xi)
  exact ⟨{ family := Gamma
           sphere_parameter_eq := hnormalized.2
           class_eq := hclass }⟩

theorem m59ShortLoopPiThree_of_service (P58 : RepairedShortLoopTrivialityTheory.{u})
    (S : M59IdentificationSystem.{u}) : M59ShortLoopPiThreeClaim S := by
  intro M _ _ _ _ _ g compact connected x pi_two_trivial
  let e := (S.core compact connected x pi_two_trivial).pi_two_pi_three
  obtain ⟨zeta, hzeta, hshort⟩ :=
    P58.short_loop.short_loop_family_trivial g compact x pi_two_trivial
  refine ⟨zeta, hzeta, ?_⟩
  intro xi Gamma hclass hlength
  have hbase : Gamma.basepoint = x := congrArg Sigma.fst hclass
  have hzero := hshort Gamma hbase hlength
  cases hbase
  have hvalue : Gamma.homotopy_class = e.symm xi :=
    eq_of_heq (Sigma.mk.inj hclass).2
  apply e.symm.injective
  simpa only [map_one] using hvalue.symm.trans hzero

theorem m59ShortLoopPiThree_from_M58 (S : M59IdentificationSystem.{u}) :
    M59ShortLoopPiThreeClaim S :=
  m59ShortLoopPiThree_of_service repairedShortLoopTriviality S

theorem m59BasepointTransport_from_M59
    (hM59 : M59LoopClassesAndComponentTopologyTheory.{u}) :
    Nonempty M59HigherBasepointTransportService.{u} := by
  obtain ⟨_S, _representative, _short_loop, basepoint_service⟩ := hM59
  exact basepoint_service






theorem m59BasepointTransport_bijective
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    (B : M59HigherBasepointTransport X n)
    {x y : X} (p : Path x y) :
    Function.Bijective (M59HigherBasepointTransport.map B p) := by
  constructor
  · intro a b hab
    have h := congrArg (M59HigherBasepointTransport.map B p.symm) hab
    have ha := B.map_left_inverse p a
    have hb := B.map_left_inverse p b
    exact ha.symm.trans (h.trans hb)
  · intro b
    refine ⟨M59HigherBasepointTransport.map B p.symm b, ?_⟩
    have h := B.map_left_inverse p.symm b
    simpa using h

theorem m59BasepointTransport_nonzero
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    (B : M59HigherBasepointTransport X n)
    {x y : X} (p : Path x y) [Nonempty (Fin n)]
    {a : HomotopyGroup.Pi n X x} (ha : a ≠ 1) :
    M59HigherBasepointTransport.map B p a ≠ 1 := by
  intro h
  apply ha
  apply (m59BasepointTransport_bijective B p).1
  exact h.trans (B.map_one p).symm

end PoincareConjecture
