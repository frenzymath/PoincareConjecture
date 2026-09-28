import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.ParentMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.Precomposition
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Rebasing.Represents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow} {T : ℝ}
  {P : RepairedComponentPath D.flow T W}
  {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
  {H : RepairedAncestryTransportInput D W P K C}
  (B : M59HigherBasepointTransportService)
  (A : RepairedAncestryTransportData D W P K C H B)
  (Syst : M59IdentificationSystem.{u})
  (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
  (hpost : Nonempty (D.flow.slice S.1).carrier)
  (hdelta : D.flow.parameters.delta S.1 < repairedComparisonDeltaBound D.flow.local_constants)
  (hh : D.flow.parameters.h S.1 < repairedComparisonHeightBound D.flow.local_constants)
  (eta : ℝ) (heta : 0 < eta)

theorem m67_event_transport_of_approximant
    (s : Set.Icc (0 : ℝ) T)
    (hs : (D.flow.event S.1 hS).tMinus < s.1) (hsS : s.1 < S.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event S.1 hS).tMinus s.1))
    (pre : M67WidthSlice Syst.quotient (P.component s))
    (hambient : pre.ambient_metric = D.flow.metric s.1)
    (post : M67WidthSlice Syst.quotient (H.event_input S hS hpost).child)
    (hpostmetric : post.metric = (H.event_input S hS hpost).child_metric)
    (f : ContinuousMap (H.event_input S hS hpost).parent.carrier.carrier
      (H.event_input S hS hpost).child.carrier.carrier)
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hhom : f.Homotopic (A.event_output S hS hpost hdelta hh).comparison.map)
    (hbound : ∀ x y, (H.event_input S hS hpost).child_metric.edist (f x) (f y) ≤
      ENNReal.ofReal (1 + eta) * ((H.event_input S hS hpost).parent_metric s.1).edist x y)
    (hclass : M67AlphaTransport B (P.component s).basepoint
      (H.event_input S hS hpost).child.basepoint
      (f.comp (repairedDiffeomorphContinuousMap (m67EventPreToParent H S hS hpost s hs hJ)))
      pre.alpha post.alpha) :
    Nonempty {E : M67EventTransport B A Syst.quotient S s hS hpost hdelta hh eta heta //
      E.pre = pre ∧ E.post = post} := by
  let e := m67EventPreToParent H S hS hpost s hs hJ
  let F := f.comp (repairedDiffeomorphContinuousMap e)
  have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F := hf.comp e.contMDiff
  obtain ⟨L, p, lp, htransport⟩ := hclass
  have hmetric := m67EventPreToParent_metric H S hS hpost s hs hsS hJ pre hambient
  have hdist : ∀ x y, post.metric.edist (F x) (F y) ≤
      ENNReal.ofReal (1 + eta) * pre.metric.edist x y := by
    intro x y
    rw [hpostmetric]
    exact m67_distance_bound_comp_of_pullback pre.metric
      ((H.event_input S hS hpost).parent_metric s.1)
      (H.event_input S hS hpost).child_metric
      (repairedDiffeomorphContinuousMap e) e.contMDiff hmetric f hbound x y
  refine ⟨⟨{
    pre := pre
    post := post
    pretime_lt := hs
    pre_no_surgery := hJ
    parent_identification := m67EventParentIdentification H S hS hpost
    parent_identification_eq := m67EventParentIdentification_inclusion H S hS hpost
    parent_identification_based :=
      (Path.refl (H.event_input S hS hpost).parent.basepoint).cast
        (m67EventParentIdentification_basepoint H S hS hpost) rfl
    pre_to_parent := e
    pre_to_parent_eq_regular := fun _ => rfl
    pre_metric_eq_parent := hmetric
    f := F
    smooth := hF
    based_path := p
    loop_basepoint_path := lp
    loop := L
    class_transport := htransport
    null_transport := m67_null_transport_of_postcomposition F L
    comparison_homotopy := hhom.comp (ContinuousMap.Homotopic.refl _)
    child_metric_eq := hpostmetric
    distance_bound := hdist
    filling_transport := m67_filling_transport_of_distance_bound pre.metric post.metric
      F hF L heta hdist
    represents_transport := ?_ }, rfl, rfl⟩⟩
  intro family _hnull hrep
  have h := m67_represents_postcomposition_rebase Syst B F hF L
    (P.component s).basepoint (H.event_input S hS hpost).child.basepoint
    (Syst.core (H.event_input S hS hpost).child.compact
      (H.event_input S hS hpost).child.connected
      (H.event_input S hS hpost).child.basepoint post.pi_two_trivial)
    pre.alpha lp.loop family hrep
  rw [htransport] at h
  exact h

theorem m67_event_transport_family_exists
    (pre : ∀ s : Set.Icc (0 : ℝ) T, M67WidthSlice Syst.quotient (P.component s))
    (hambient : ∀ s, (pre s).ambient_metric = D.flow.metric s.1)
    (post : M67WidthSlice Syst.quotient (H.event_input S hS hpost).child)
    (hpostmetric : post.metric = (H.event_input S hS hpost).child_metric)
    (hclasses : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : (D.flow.event S.1 hS).tMinus < s.1) (_hsS : s.1 < S.1)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event S.1 hS).tMinus s.1))
      (f : ContinuousMap (H.event_input S hS hpost).parent.carrier.carrier
        (H.event_input S hS hpost).child.carrier.carrier)
      (_hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
      (hbase : f (H.event_input S hS hpost).parent.basepoint =
        (A.event_output S hS hpost hdelta hh).comparison.target_basepoint),
      (∀ alpha, surgeryHomotopyMap (n := 3) f hbase alpha =
        surgeryHomotopyMap (A.event_output S hS hpost hdelta hh).comparison.map
          (A.event_output S hS hpost hdelta hh).comparison.based alpha) →
      M67AlphaTransport B (P.component s).basepoint
        (H.event_input S hS hpost).child.basepoint
        (f.comp (repairedDiffeomorphContinuousMap (m67EventPreToParent H S hS hpost s hs hJ)))
        (pre s).alpha post.alpha) :
    Nonempty {F : M67EventTransportFamily B A Syst.quotient S hS hpost hdelta hh eta heta //
      ∀ s hnear hbefore hafter hJ,
        (F.transport s hnear hbefore hafter hJ).pre = pre s ∧
        (F.transport s hnear hbefore hafter hJ).post = post} := by
  classical
  obtain ⟨delta, hd, happ⟩ :=
    (A.event_output S hS hpost hdelta hh).smooth_approximants eta heta
  have each (s : Set.Icc (0 : ℝ) T) (hnear : S.1 - delta < s.1)
      (hbefore : s.1 < S.1) (hafter : (D.flow.event S.1 hS).tMinus < s.1)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event S.1 hS).tMinus s.1)) :
      Nonempty {E : M67EventTransport B A Syst.quotient S s hS hpost hdelta hh eta heta //
        E.pre = pre s ∧ E.post = post} := by
    obtain ⟨f, hf, ⟨hbase, hpi⟩, hhom, hbound, _hdegree⟩ := happ s.1 hnear hbefore
    exact m67_event_transport_of_approximant B A Syst S hS hpost hdelta hh eta heta
      s hafter hbefore hJ (pre s) (hambient s) post hpostmetric f hf hhom hbound
      (hclasses s hafter hbefore hJ f hf hbase hpi)
  refine ⟨⟨{
    delta := delta
    delta_pos := hd
    transport := fun s hnear hbefore hafter hJ =>
      (Classical.choice (each s hnear hbefore hafter hJ)).val }, ?_⟩⟩
  intro s hnear hbefore hafter hJ
  exact (Classical.choice (each s hnear hbefore hafter hJ)).property

end PoincareConjecture
