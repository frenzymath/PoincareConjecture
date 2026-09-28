import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.ClassPath.Data

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

theorem m67_pi_two_trivial_of_homotopy_equivalence
    (B : M59HigherBasepointTransportService.{u})
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [SimplyConnectedSpace M] [SimplyConnectedSpace N]
    (f : C(M, N)) (he : ∃ e : ContinuousMap.HomotopyEquiv M N, e.toFun = f)
    (x : M) (y : N) (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) :
    Subsingleton (HomotopyGroup.Pi 2 N y) := by
  have hf := (SurgeryComparison.Topology.surgeryHomotopyMap_bijective_of_homotopyEquiv
    1 f (rfl : f x = f x) he).2
  let p : Path (f x) y := PathConnectedSpace.somePath _ _
  have hp := (m59BasepointTransport_bijective (B.transport 2) p).2
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hp a
  obtain ⟨b', rfl⟩ := hp b
  obtain ⟨a'', rfl⟩ := hf a'
  obtain ⟨b'', rfl⟩ := hf b'
  rw [hpi.elim a'' b'']

theorem m67_alpha_transport_of_based_postcomposition
    (B : M59HigherBasepointTransportService.{u})
    {M N : Type u}
    [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
    (f : C(M, N)) (L : M59LoopPostcomposition f) (x : M) {z : N}
    (hbase : f x = z) (y : N) (p : Path z y)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    M67AlphaTransport B x y f alpha
      (M59HigherBasepointTransport.map (B.transport 2) (m67ConstantLoopPath p).loop
        (surgeryHomotopyMap L.map (L.map_based hbase) alpha)) := by
  subst z
  exact ⟨L, p, m67ConstantLoopPath p, rfl⟩

theorem m67_event_class_datum_exists
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {t : ℝ} {ht : t ∈ D.flow.surgery_times}
    [Nonempty (D.flow.slice t).carrier]
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (I : RepairedComparisonHomotopyInput D t ht)
    (O : RepairedComparisonHomotopyConclusion I)
    (x : M67ClassDatum S I.parent) :
    ∃ y : M67ClassDatum S I.child,
      ∀ (f : C(I.parent.carrier.carrier, I.child.carrier.carrier))
        (_hsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
        (hbase : f I.parent.basepoint = O.comparison.target_basepoint),
        (∀ alpha, surgeryHomotopyMap (n := 3) f hbase alpha =
          surgeryHomotopyMap O.comparison.map O.comparison.based alpha) →
        M67AlphaTransport B I.parent.basepoint I.child.basepoint f x.alpha y.alpha := by
  let := I.parent_simply_connected
  let := I.child_simply_connected
  let z := O.comparison.target_basepoint
  let hpiz := m67_pi_two_trivial_of_homotopy_equivalence B O.comparison.map
    O.homotopy_equivalence I.parent.basepoint z x.pi_two_trivial
  let hpiy := m67_pi_two_trivial_of_homotopy_equivalence B O.comparison.map
    O.homotopy_equivalence I.parent.basepoint I.child.basepoint x.pi_two_trivial
  let CM := S.core I.parent.compact I.parent.connected I.parent.basepoint x.pi_two_trivial
  let CZ := S.core I.child.compact I.child.connected z hpiz
  let CY := S.core I.child.compact I.child.connected I.child.basepoint hpiy
  let a : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := I.child.carrier.carrier))
      (constantC1Loop z) :=
    CZ.pi_two_pi_three.symm
      (surgeryHomotopyMap O.comparison.map O.comparison.based
        (CM.pi_two_pi_three x.alpha))
  let p : Path z I.child.basepoint := PathConnectedSpace.somePath _ _
  let beta := M59HigherBasepointTransport.map (B.transport 2)
    (m67ConstantLoopPath p).loop a
  have ha : a ≠ 1 := by
    intro ha
    have heq : surgeryHomotopyMap O.comparison.map O.comparison.based
        (CM.pi_two_pi_three x.alpha) = 1 := by
      have h := congrArg CZ.pi_two_pi_three ha
      simpa only [a, MulEquiv.apply_symm_apply, map_one] using h
    apply x.nonzero
    apply O.pi_three_bijective.1
    rw [heq]
    have hmap : surgeryHomotopyMap (n := 3) O.comparison.map O.comparison.based
        (1 : HomotopyGroup.Pi 3 I.parent.carrier.carrier I.parent.basepoint) = 1 := by
      apply congrArg Quotient.mk'
      apply GenLoop.ext
      intro w
      exact O.comparison.based
    exact hmap.symm
  have hbeta : beta ≠ 1 :=
    m59BasepointTransport_nonzero (B.transport 2) (m67ConstantLoopPath p).loop ha
  have hnonzero : CY.pi_two_pi_three beta ≠ 1 := by
    intro h
    apply hbeta
    apply CY.pi_two_pi_three.injective
    exact h.trans CY.pi_two_pi_three.map_one.symm
  refine ⟨⟨hpiy, beta, hnonzero⟩, ?_⟩
  intro f hsmooth hbase hmap
  obtain ⟨L⟩ := S.postcomposition f hsmooth
  have heq : surgeryHomotopyMap (n := 2) L.map (L.map_based hbase) x.alpha = a := by
    apply CZ.pi_two_pi_three.injective
    rw [S.naturality I.parent.compact I.parent.connected I.child.compact
      I.child.connected I.parent.basepoint z x.pi_two_trivial hpiz f hsmooth hbase L]
    exact (hmap _).trans (CZ.pi_two_pi_three.apply_symm_apply _).symm
  have htransport := m67_alpha_transport_of_based_postcomposition B f L
    I.parent.basepoint hbase I.child.basepoint p x.alpha
  rw [heq] at htransport
  exact htransport

noncomputable def m67EventClassDatum
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {t : ℝ} {ht : t ∈ D.flow.surgery_times}
    [Nonempty (D.flow.slice t).carrier]
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (I : RepairedComparisonHomotopyInput D t ht)
    (O : RepairedComparisonHomotopyConclusion I)
    (x : M67ClassDatum S I.parent) : M67ClassDatum S I.child :=
  (m67_event_class_datum_exists S B I O x).choose

theorem m67EventClassDatum_transport
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {t : ℝ} {ht : t ∈ D.flow.surgery_times}
    [Nonempty (D.flow.slice t).carrier]
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (I : RepairedComparisonHomotopyInput D t ht)
    (O : RepairedComparisonHomotopyConclusion I)
    (x : M67ClassDatum S I.parent)
    (f : C(I.parent.carrier.carrier, I.child.carrier.carrier))
    (hsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hbase : f I.parent.basepoint = O.comparison.target_basepoint)
    (hmap : ∀ alpha, surgeryHomotopyMap (n := 3) f hbase alpha =
      surgeryHomotopyMap O.comparison.map O.comparison.based alpha) :
    M67AlphaTransport B I.parent.basepoint I.child.basepoint f x.alpha
      (m67EventClassDatum S B I O x).alpha :=
  (m67_event_class_datum_exists S B I O x).choose_spec f hsmooth hbase hmap

end PoincareConjecture
