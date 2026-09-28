import PoincareConjecture.Proofs.M47.CanonicalComponentPersistence
import PoincareConjecture.Proofs.M47.GeneralizedBridgeComponent
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_SlabScalarTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {a b : ℝ}

theorem eventually_regularSlab_component_control
    (hC : RicciFlowCurvatureTheory.{u}) (S : SurgeryRegularSlab F.slice F.metric a b)
    (ha : a ∈ F.time_domain) (t : Icc a b)
    (N : SingularCComponent (S.flow.metric t.val) (S.flow.connection t.val) F.parameters.C) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∀ x ∈ N.carrier,
      SurgeryCanonicalControl F s.val (S.identify s x)
        F.parameters.epsilon F.parameters.C := by
  let : CompactSpace (F.slice a).carrier := isCompact_univ_iff.mp (F.slices_compact a ha)
  filter_upwards [eventually_same_C_component hC S.flow t N] with s hs
  obtain ⟨P, hPcarrier, _⟩ := hs
  let H := PoincareConjecture.M47.metricIsometry_pullback_C_component (S.identify s).symm
    (PoincareConjecture.M47.metricHomothety_one_symm (S.identify s)
      (M44.regularSlab_metricHomothety F S s)) (F.connection s.val) (S.flow.connection s.val) P
  intro x hx
  apply SurgeryCanonicalControl.component H
  change (S.identify s).symm (S.identify s x) ∈ P.carrier
  rw [(S.identify s).symm_apply_apply, hPcarrier]
  exact hx

theorem regularSlab_limit_not_component
    (hC : RicciFlowCurvatureTheory.{u}) (S : SurgeryRegularSlab F.slice F.metric a b)
    (ha : a ∈ F.time_domain) (t : Icc a b)
    (times : ℕ → Icc a b) (points : ℕ → (F.slice a).carrier)
    (x : (F.slice a).carrier)
    (htimes : Tendsto (fun n => (times n).val) atTop (𝓝 t.val))
    (hpoints : Tendsto points atTop (𝓝 x))
    (hbad : ∀ n, ¬ SurgeryCanonicalControl F (times n).val
      (S.identify (times n) (points n)) F.parameters.epsilon F.parameters.C)
    (N : SingularCComponent (F.metric t.val) (F.connection t.val) F.parameters.C) :
    S.identify t x ∉ N.carrier := by
  intro hx
  let : LocallyConnectedSpace (F.slice a).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (F.slice a).carrier
  let P := PoincareConjecture.M47.metricIsometry_pullback_C_component (S.identify t)
    (M44.regularSlab_metricHomothety F S t) (S.flow.connection t.val) (F.connection t.val) N
  have hxP : x ∈ P.carrier := hx
  have hopen : IsOpen P.carrier := by
    rw [P.component_eq]
    exact isOpen_connectedComponent
  have htime : Tendsto times atTop (𝓝 t) := tendsto_subtype_rng.mpr htimes
  have hcanonical := htime.eventually (eventually_regularSlab_component_control hC S ha t P)
  have hcore := hpoints.eventually (hopen.mem_nhds hxP)
  have hgood : ∀ᶠ n in atTop, SurgeryCanonicalControl F (times n).val
      (S.identify (times n) (points n)) F.parameters.epsilon F.parameters.C := by
    filter_upwards [hcanonical, hcore] with n hn hpoint
    exact hn (points n) hpoint
  obtain ⟨n, hn⟩ := hgood.exists
  exact hbad n hn

end PoincareConjecture.Proofs.M47
