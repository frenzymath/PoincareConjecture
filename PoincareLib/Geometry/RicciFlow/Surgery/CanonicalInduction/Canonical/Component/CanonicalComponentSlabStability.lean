import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Canonical.Component.CanonicalComponentPersistence
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeComponent
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Bounds.SlabScalarTransport

/-!
# Actual regular-slab component stability at the first-failure limit

The complete ordinary C-component keeps its open carrier. Actual slab
isometries give physical canonical control there and exclude this
alternative at a limit of noncanonical points. MT Lemma 17.2, p. 396.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M47

variable {F : SurgeryFlowData.{u}} {a b : ℝ}

/-- One time neighborhood gives physical canonical control throughout
the unchanged ordinary component, with the original fixed C. -/
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
  let H := PoincareMT.M47.metricIsometry_pullback_C_component (S.identify s).symm
    (PoincareMT.M47.metricHomothety_one_symm (S.identify s)
      (M44.regularSlab_metricHomothety F S s)) (F.connection s.val) (S.flow.connection s.val) P
  intro x hx
  apply SurgeryCanonicalControl.component H
  change (S.identify s).symm (S.identify s x) ∈ P.carrier
  rw [(S.identify s).symm_apply_apply, hPcarrier]
  exact hx

/-- A limit of physical noncanonical points cannot lie in an actual
C-component at the tested C, MT Lemma 17.2, p. 396. -/
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
  let P := PoincareMT.M47.metricIsometry_pullback_C_component (S.identify t)
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

end PoincareMT.Proofs.M47
