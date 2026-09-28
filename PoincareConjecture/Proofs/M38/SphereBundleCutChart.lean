import PoincareConjecture.Proofs.M38.SphereBundleCutComponents
import PoincareConjecture.Proofs.M38.CompactCoverSheet
import PoincareConjecture.Proofs.M38.SphericalModelRegions
import PoincareConjecture.Proofs.M38.CylinderSphereFilling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

theorem exists_spherical_chart_of_global_cylinder
    (A : GeneralizedSliceCarrier.{u})
    (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace A.carrier ∞) :
    ∃ e : OpenPartialHomeomorph A.carrier sphereCarrier.{u}.carrier,
      e.source = univ ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
  let l : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace euclideanCarrier.{u}.carrier ∞ := {
    toEquiv := (Homeomorph.ulift : euclideanCarrier.{u}.carrier ≃ₜ StandardCapSpace).symm.toEquiv
    contMDiff_toFun := threeManifold_up_contMDiff StandardCapSpace
    contMDiff_invFun := threeManifold_down_contMDiff StandardCapSpace }
  let j := (D.symm.toPartialDiffeomorph.trans Poincare.radialPartialDiffeomorph).trans
    l.toPartialDiffeomorph
  have hjs : j.source = univ := by
    simp [j, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph]
  obtain ⟨e, he, hs, hi⟩ := exists_spherical_chart_of_euclidean_region
    (partialHomeomorphRegions j.toOpenPartialHomeomorph
      j.contMDiffOn_toFun j.contMDiffOn_invFun) j.open_source j.open_target
  exact ⟨e, he.trans hjs, hs, hi⟩

theorem sphereBundle_cut_connected_spherical_chart
    (Q : GeneralizedSliceCarrier.{u}) [CompactSpace Q.carrier] (B : SurgerySphereBundle Q)
    (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace
      (circlePullbackCarrier Q B.projection B.projection_smooth).carrier ∞)
    {K : Set Q.carrier} (hK : IsConnected K)
    (havoid : Disjoint K (range (fun z : UnitTwoSphere =>
      circlePullbackProjection Q B.projection B.projection_smooth (D (z, 0))))) :
    ∃ e : OpenPartialHomeomorph Q.carrier sphereCarrier.{u}.carrier,
      K ⊆ e.source ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
  let A := circlePullbackCarrier Q B.projection B.projection_smooth
  let q := circlePullbackProjection Q B.projection B.projection_smooth
  let U := (range (fun z : UnitTwoSphere => q (D (z, 0))))ᶜ
  have hq := circlePullback_projection_localDiffeomorph Q B.projection B.projection_smooth
  obtain ⟨b, hb⟩ := hK.nonempty
  obtain ⟨a, ha⟩ := CirclePullback.projection_surjective B.projection b
  change q a = b at ha
  have hU : IsOpen U := (isCompact_range
    (hq.contMDiff.continuous.comp (D.contMDiff.continuous.comp
      (continuous_id.prodMk continuous_const)))).isClosed.isOpen_compl
  have hKU : K ⊆ U := disjoint_left.mp havoid
  have hKa : q a ∈ K := ha.symm ▸ hb
  let C := connectedComponentIn (q ⁻¹' U) a
  let : Nonempty A.carrier := ⟨a⟩
  let : LocallyConnectedSpace A.carrier := ChartedSpace.locallyConnectedSpace StandardCapSpace _
  have hcompact : IsCompact (closure C) := sphereBundle_cut_component_precompact Q B D a
  have hKC : K ⊆ q '' C := connected_subset_image_precompact_component q
    hq.contMDiff.continuous hq.isLocalHomeomorph.isOpenMap hU (hKU hKa)
    hcompact hK.isPreconnected hKU hKa
  obtain ⟨d, hds, hdt, _⟩ := localDiffeomorph_injective_open_sheet q hq
    (hU.preimage hq.contMDiff.continuous).connectedComponentIn
    (sphereBundle_cut_component_injective Q B D a)
  obtain ⟨s, hss, hs, hi⟩ := exists_spherical_chart_of_global_cylinder A D
  let s' : PartialDiffeomorph (𝓡 3) (𝓡 3) A.carrier sphereCarrier.{u}.carrier ∞ := {
    toPartialEquiv := s.toPartialEquiv
    open_source := s.open_source
    open_target := s.open_target
    contMDiffOn_toFun := hs
    contMDiffOn_invFun := hi }
  let e := d.symm.trans s'
  refine ⟨e.toOpenPartialHomeomorph, ?_, e.contMDiffOn_toFun, e.contMDiffOn_invFun⟩
  intro y hy
  refine ⟨hdt.symm ▸ hKC hy, ?_⟩
  change d.symm y ∈ s.source
  rw [hss]
  exact mem_univ _

end PoincareConjecture.M38
