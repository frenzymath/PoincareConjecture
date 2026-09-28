import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.ComponentTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Reference

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

def SmoothClosedComponentModel.restrictToOpen {kind : ClosedComponentKind} {Y : Set M}
    (K : SmoothClosedComponentModel kind Y) (U : Opens M) (hYU : Y ⊆ U) :
    SmoothClosedComponentModel kind ((Subtype.val : U → M) ⁻¹' Y) where
  model := K.model
  model_topology := K.model_topology
  model_charted := K.model_charted
  model_manifold := K.model_manifold
  standard_model := K.standard_model
  standard_smooth := K.standard_smooth
  forward := fun y => ⟨K.forward y, hYU (K.forward_mem y)⟩
  inverse := fun x => K.inverse x.val
  forward_mem := fun y => K.forward_mem y
  left_inverse := fun x hx => Subtype.ext (K.left_inverse x.val hx)
  right_inverse := K.right_inverse
  forward_smooth := by
    let := K.model_topology
    let := K.model_charted
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact K.forward_smooth
  inverse_smooth := by
    let := K.model_topology
    let := K.model_charted
    exact K.inverse_smooth.comp contMDiff_subtype_val.contMDiffOn (fun _ hx => hx)

def ClosedComponentCertificate.restrictToOpen {kind : ClosedComponentKind} {Y : Set M}
    (K : ClosedComponentCertificate kind Y) (U : Opens M) (hYU : Y ⊆ U) :
    ClosedComponentCertificate kind ((Subtype.val : U → M) ⁻¹' Y) where
  model := K.model
  homeomorph := by
    letI := K.model.carrier_topology
    have hi : Topology.IsEmbedding (Subtype.val : U → M) := .subtypeVal
    exact (hi.homeomorphOfSubsetRange (fun y hy => ⟨⟨y, hYU hy⟩, rfl⟩)).trans K.homeomorph
  connected := by
    constructor
    · obtain ⟨x, hx⟩ := K.connected.nonempty
      exact ⟨⟨x, hYU hx⟩, hx⟩
    · have hi : Topology.IsInducing (Subtype.val : U → M) := .subtypeVal
      apply hi.isPreconnected_image.mp
      have himage : (Subtype.val : U → M) '' ((Subtype.val : U → M) ⁻¹' Y) = Y :=
        Set.image_preimage_eq_of_subset (fun y hy => ⟨⟨y, hYU hy⟩, rfl⟩)
      rw [himage]
      exact K.connected.isPreconnected
  compact := Topology.IsInducing.subtypeVal.isCompact_preimage' K.compact
    (by simpa only [Subtype.range_coe] using hYU)
  component := by
    obtain ⟨x, hx⟩ := K.component
    have hxU : x ∈ U := hYU (hx ▸ mem_connectedComponent)
    refine ⟨⟨x, hxU⟩, ?_⟩
    rw [SingularRegularLimit.connectedComponent_subtype_eq_preimage
      (⟨x, hxU⟩ : U) (by simpa only [← hx] using hYU)]
    rw [hx]
    rfl
  smooth_model := K.smooth_model.restrictToOpen U hYU
  model_transport := by
    obtain ⟨e, he⟩ := K.model_transport
    refine ⟨e, fun x => ?_⟩
    exact he ⟨x.val.val, x.property⟩

def ClosedComponentCertificate.restrictToComponent {kind : ClosedComponentKind} {Y : Set M}
    (K : ClosedComponentCertificate kind Y) (U : Opens M) (hYU : Y ⊆ U)
    (x : U) (hx : (x : M) ∈ Y) :
    ClosedComponentCertificate kind (connectedComponent x) := by
  have heq : ((Subtype.val : U → M) ⁻¹' Y) = connectedComponent x := by
    obtain ⟨p, hp⟩ := K.component
    have hcomp : Y = connectedComponent (x : M) :=
      hp.trans (connectedComponent_eq (hp ▸ hx))
    rw [SingularRegularLimit.connectedComponent_subtype_eq_preimage x
      (by simpa only [← hcomp] using hYU), hcomp]
    rfl
  exact heq ▸ K.restrictToOpen U hYU

theorem SingularCComponent.topology_restrictToOpen
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {C : ℝ}
    (N : SingularCComponent g D C) (U : Opens M) (hNU : N.carrier ⊆ U)
    (x : U) (hx : (x : M) ∈ N.carrier) :
    Nonempty (ClosedComponentCertificate ClosedComponentKind.threeSphere
      (connectedComponent x)) ∨
      Nonempty (ClosedComponentCertificate ClosedComponentKind.realProjectiveThree
        (connectedComponent x)) := by
  rcases N.topology with hK | hK
  · obtain ⟨K⟩ := hK
    exact Or.inl ⟨K.restrictToComponent U hNU x hx⟩
  · obtain ⟨K⟩ := hK
    exact Or.inr ⟨K.restrictToComponent U hNU x hx⟩

namespace SingularTimeAssumptions

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminal_topology_of_frequently_cComponent
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier) :
    IsCompact (connectedComponent x) ∧
      (Nonempty (ClosedComponentCertificate ClosedComponentKind.threeSphere
        (connectedComponent x)) ∨
        Nonempty (ClosedComponentCertificate ClosedComponentKind.realProjectiveThree
          (connectedComponent x))) := by
  obtain ⟨s, hsref, hsT, hcap⟩ := H.exists_late_cComponent_terminal_carrier P04 x
  have hsEv : ∀ᶠ t in 𝓝[<] T, s ≤ t :=
    (eventually_ge_nhds hsT).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨ht, N, hxN⟩, hst⟩ := (hfreq.and_eventually hsEv).exists
  obtain ⟨_, hreg, _, hcompact⟩ := hcap t ht hst N hxN
  let N' := H.reference.referenceCComponent t ht N
  have hcarrier : N'.carrier = connectedComponent (x : M) :=
    H.reference.referenceCComponent_carrier t ht N hxN
  have hNU : N'.carrier ⊆ H.regularRegion P04 := by
    rw [hcarrier]
    exact hreg
  have hx' : (x : M) ∈ N'.carrier := by
    rw [hcarrier]
    exact mem_connectedComponent
  exact ⟨hcompact, N'.topology_restrictToOpen (H.regularRegion P04) hNU x hx'⟩

end SingularTimeAssumptions

end PoincareConjecture
