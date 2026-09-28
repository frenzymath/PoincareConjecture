import PoincareConjecture.Proofs.M47.CanonicalRoundPersistence
import PoincareConjecture.Proofs.M47.GeneralizedBridgeRound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_SlabScalarTransport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {a b : ℝ}



theorem eventually_regularSlab_round_control (S : SurgeryRegularSlab F.slice F.metric a b)
    (t : Icc a b)
    (N : SingularRoundComponent (S.flow.metric t.val) F.parameters.epsilon) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∀ x ∈ N.carrier,
      SurgeryCanonicalControl F s.val (S.identify s x)
        F.parameters.epsilon F.parameters.C := by
  filter_upwards [eventually_same_round_component S.flow t N] with s hs
  obtain ⟨P, hPcarrier, _⟩ := hs
  let H := PoincareConjecture.M47.metricIsometry_pullback_round_component (S.identify s).symm
    (PoincareConjecture.M47.metricHomothety_one_symm (S.identify s)
      (M44.regularSlab_metricHomothety F S s)) P
  intro x hx
  apply SurgeryCanonicalControl.round H
  change S.identify s x ∈ S.identify s '' P.carrier
  refine ⟨x, ?_, rfl⟩
  rwa [hPcarrier]



theorem regularSlab_limit_not_round (S : SurgeryRegularSlab F.slice F.metric a b)
    (t : Icc a b) (times : ℕ → Icc a b) (points : ℕ → (F.slice a).carrier)
    (x : (F.slice a).carrier)
    (htimes : Tendsto (fun n ↦ (times n).val) atTop (𝓝 t.val))
    (hpoints : Tendsto points atTop (𝓝 x))
    (hbad : ∀ n, ¬ SurgeryCanonicalControl F (times n).val
      (S.identify (times n) (points n)) F.parameters.epsilon F.parameters.C)
    (N : SingularRoundComponent (F.metric t.val) F.parameters.epsilon) :
    S.identify t x ∉ N.carrier := by
  intro hx
  let : LocallyConnectedSpace (F.slice a).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (F.slice a).carrier
  let P := PoincareConjecture.M47.metricIsometry_pullback_round_component (S.identify t)
    (M44.regularSlab_metricHomothety F S t) N
  have hxP : x ∈ P.carrier :=
    ⟨S.identify t x, hx, (S.identify t).symm_apply_apply x⟩
  have hopen : IsOpen P.carrier := by
    rw [P.component_eq]
    exact isOpen_connectedComponent
  have htime : Tendsto times atTop (𝓝 t) := tendsto_subtype_rng.mpr htimes
  have hcanonical := htime.eventually (eventually_regularSlab_round_control S t P)
  have hcore := hpoints.eventually (hopen.mem_nhds hxP)
  have hgood : ∀ᶠ n in atTop, SurgeryCanonicalControl F (times n).val
      (S.identify (times n) (points n)) F.parameters.epsilon F.parameters.C := by
    filter_upwards [hcanonical, hcore] with n hn hpoint
    exact hn (points n) hpoint
  obtain ⟨n, hn⟩ := hgood.exists
  exact hbad n hn

end PoincareConjecture.Proofs.M47
