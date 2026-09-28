import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Covering
import PoincareConjecture.Proofs.Horizon.Topology.Covering.OpenLift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Regions
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Quotient.Circle

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.SphereBundleCircleModel

theorem isOpenMap_projection (B : SphereBundleCircleModel.{u}) :
    letI := B.carrier_topology
    IsOpenMap B.projection := by
  let := B.carrier_topology
  let := B.carrier_charted
  let := B.carrier_manifold
  intro S hS
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨U, hU, hxU, f, g, himage, hleft, hright, hf, hg, hproj⟩ :=
    B.local_trivialization (B.projection x)
  let e : OpenPartialHomeomorph B.carrier (UnitTwoSphere × UnitCircle) := {
    toFun := f
    invFun := g
    source := B.projection ⁻¹' U
    target := univ ×ˢ U
    map_source' := fun y hy => himage ▸ mem_image_of_mem f hy
    map_target' := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := himage.symm ▸ hz
      simpa only [hleft hy] using hy
    left_inv' := hleft
    right_inv' := hright
    open_source := hU.preimage B.projection_continuous
    open_target := isOpen_univ.prod hU
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hg.continuousOn }
  have hopen : IsOpen (Prod.snd '' (e '' (S ∩ e.source))) :=
    isOpenMap_snd _ (e.isOpen_image_of_subset_source (hS.inter e.open_source)
      inter_subset_right)
  have hximage : B.projection x ∈ Prod.snd '' (e '' (S ∩ e.source)) :=
    ⟨f x, ⟨x, ⟨hx, hxU⟩, rfl⟩, hproj x hxU⟩
  apply mem_of_superset (hopen.mem_nhds hximage)
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨y, hy.1, (hproj y hy.2).symm⟩

theorem not_compactSpace_of_continuous_open_map
    (B : SphereBundleCircleModel.{u}) {E : Type*} [TopologicalSpace E]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E] :
    letI := B.carrier_topology
    ∀ q : E → B.carrier, Continuous q → IsOpenMap q → ¬ CompactSpace E := by
  let := B.carrier_topology
  intro q hq hqopen hcompact
  let : CompactSpace E := hcompact
  let x₀ : E := Classical.choice inferInstance
  let p : C(E, UnitCircle) := ⟨B.projection ∘ q, B.projection_continuous.comp hq⟩
  obtain ⟨r, hr⟩ := unitCircleExp_surjective (p x₀)
  obtain ⟨F, ⟨_, hF⟩, _⟩ :=
    isCoveringMap_unitCircleExp.existsUnique_continuousMap_lifts p x₀ r hr
  have hopen : IsOpenMap F :=
    isCoveringMap_unitCircleExp.isLocalHomeomorph.isOpenMap_lift F.continuous
      (by rw [hF]; exact B.isOpenMap_projection.comp hqopen)
  have hK : IsCompact (range F) := isCompact_range F.continuous
  have hfull : range F = univ :=
    (show IsClopen (range F) from ⟨hK.isClosed, hopen.isOpen_range⟩).eq_univ
      (range_nonempty F)
  exact noncompact_univ ℝ (hfull ▸ hK)

theorem not_compactSpace_covering
    (B : SphereBundleCircleModel.{u}) {E : Type*} [TopologicalSpace E]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E] :
    letI := B.carrier_topology
    ∀ q : E → B.carrier, IsCoveringMap q → ¬ CompactSpace E := by
  let := B.carrier_topology
  intro q hq
  exact B.not_compactSpace_of_continuous_open_map q hq.continuous hq.isOpenMap

end PoincareConjecture.SphereBundleCircleModel

namespace PoincareConjecture.SphereBundleCircleCertificate

open Poincare.Topology

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [CompactSpace M] [ConnectedSpace M] {g : RiemannianMetric 3 M}

theorem not_whole_of_compact_positive_sectional {X : Set M}
    (C : SphereBundleCircleCertificate g X) (D : LeviCivitaData g)
    (hc : MetricComplete g)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) : C.carrier ≠ univ := by
  intro hwhole
  let := C.model.carrier_topology
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let : SemilocallySimplyConnectedSpace M :=
    semilocallySimplyConnectedSpace_of_chartedSpace 3 M
  let x₀ : M := Classical.choice inferInstance
  let := UniversalCover.chartedSpace x₀
  let := UniversalCover.isManifold x₀
  let : LocallyPathConnectedSpace (UniversalCover x₀) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) (UniversalCover x₀)
  let e : M ≃ₜ C.model.carrier := (Homeomorph.Set.univ M).symm.trans
    ((Homeomorph.setCongr hwhole.symm).trans C.homeomorph)
  exact C.model.not_compactSpace_of_continuous_open_map
    (e ∘ UniversalCover.proj (x₀ := x₀))
    (e.continuous.comp (UniversalCover.continuous_proj x₀))
    (e.isOpenMap.comp (UniversalCover.isCoveringMap x₀).isOpenMap)
    (UniversalCover.compactSpace_of_positive_sectional g D hc hsec x₀)

end PoincareConjecture.SphereBundleCircleCertificate
