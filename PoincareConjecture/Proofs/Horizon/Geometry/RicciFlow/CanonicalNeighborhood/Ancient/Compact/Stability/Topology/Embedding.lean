import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.LimitEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace NormalizedKappaSpacetimeEmbedding

variable {kappa : ℝ} {source target : BasedKappaSolution kappa}
  {J : Set ℝ} {U : Set target.carrier.carrier}
  (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (J ×ˢ U))
  {t : ℝ} (ht : t ∈ J)

theorem spatial_inverse_contMDiffOn (ht : t ∈ J) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun y ↦ (e.inverse (t, y)).2)
      ((fun x ↦ (e.toFun (t, x)).2) '' U) := by
  have hmaps : MapsTo (fun y : source.carrier.carrier ↦ (t, y))
      ((fun x ↦ (e.toFun (t, x)).2) '' U) (e.toFun '' (J ×ˢ U)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(t, x), ⟨ht, hx⟩, Prod.ext (e.time_preserving t x) rfl⟩
  intro y hy
  exact ((e.smooth_inverse_on.comp
    (contMDiff_const.prodMk contMDiff_id).contMDiffOn hmaps) y hy).snd

noncomputable def spatialHomeomorph (hU : IsOpen U) :
    OpenPartialHomeomorph target.carrier.carrier source.carrier.carrier := by
  let f := fun x ↦ (e.toFun (t, x)).2
  let g := fun y ↦ (e.inverse (t, y)).2
  have hleft (x : target.carrier.carrier) (hx : x ∈ U) : g (f x) = x := by
    have hp : e.toFun (t, x) = (t, f x) := Prod.ext (e.time_preserving t x) rfl
    simpa only [hp] using congrArg Prod.snd (e.left_inverse (t, x) ⟨ht, hx⟩)
  exact
    { toFun := f
      invFun := g
      source := U
      target := f '' U
      map_source' := fun x hx ↦ mem_image_of_mem f hx
      map_target' := by rintro _ ⟨x, hx, rfl⟩; simpa only [hleft x hx] using hx
      left_inv' := hleft
      right_inv' := by rintro _ ⟨x, hx, rfl⟩; rw [hleft x hx]
      open_source := hU
      open_target := e.spatial_isOpen_image hU ht
      continuousOn_toFun := fun x hx ↦
        (e.spatial_contMDiffAt hU ht hx).continuousAt.continuousWithinAt
      continuousOn_invFun := (e.spatial_inverse_contMDiffOn ht).continuousOn }

@[simp] theorem spatialHomeomorph_apply (hU : IsOpen U)
    (x : target.carrier.carrier) :
    e.spatialHomeomorph ht hU x = (e.toFun (t, x)).2 := rfl

@[simp] theorem spatialHomeomorph_symm_apply (hU : IsOpen U)
    (y : source.carrier.carrier) :
    (e.spatialHomeomorph ht hU).symm y = (e.inverse (t, y)).2 := rfl

@[simp] theorem spatialHomeomorph_source (hU : IsOpen U) :
    (e.spatialHomeomorph ht hU).source = U := rfl

@[simp] theorem spatialHomeomorph_target (hU : IsOpen U) :
    (e.spatialHomeomorph ht hU).target = ((fun x ↦ (e.toFun (t, x)).2) '' U) := rfl

theorem spatialHomeomorph_contMDiffOn (hU : IsOpen U) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.spatialHomeomorph ht hU) U :=
  fun _ hx ↦ (e.spatial_contMDiffAt hU ht hx).contMDiffWithinAt

theorem spatialHomeomorph_symm_contMDiffOn (hU : IsOpen U) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.spatialHomeomorph ht hU).symm
      (e.spatialHomeomorph ht hU).target := e.spatial_inverse_contMDiffOn ht

end NormalizedKappaSpacetimeEmbedding

end PoincareConjecture
