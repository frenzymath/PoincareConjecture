import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u
namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {tau : ℝ} {R : AncientRescaling K tau}

namespace AncientSpacetimeEmbedding

variable {L : AncientLimitFlow n} {J : Set ℝ} {U : Set L.carrier.carrier}

theorem spatialMap_mfderiv_bijective_of_time_nhds
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : J ∈ 𝓝 t) {x : L.carrier.carrier} (hx : x ∈ U) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (fun y ↦ (e.toFun (t, y)).2) x) := by
  have hi := e.spatialMap_mfderiv_injective_of_time_nhds hU ht hx
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 n) x) =
      Module.finrank ℝ (TangentSpace (𝓡 n) ((e.toFun (t, x)).2)) := by
    unfold TangentSpace
    rfl
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) ((e.toFun (t, x)).2)) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi⟩

theorem spatialMap_isOpen_image
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : J ∈ 𝓝 t) :
    IsOpen ((fun y ↦ (e.toFun (t, y)).2) '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    (e.spatialMap_contMDiffAt_of_time_nhds hU ht hx)
    (e.spatialMap_mfderiv_bijective_of_time_nhds hU ht hx)]
  exact image_mem_map (hU.mem_nhds hx)

theorem spatialInverse_contMDiffAt
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : J ∈ 𝓝 t) {x : L.carrier.carrier} (hx : x ∈ U) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun y ↦ (e.inverse (t, y)).2) (e.toFun (t, x)).2 := by
  let f : L.carrier.carrier → M := fun y ↦ (e.toFun (t, y)).2
  have hmaps : MapsTo (fun y : M ↦ (t, y)) (f '' U) (e.toFun '' (J ×ˢ U)) := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨(t, z), ⟨mem_of_mem_nhds ht, hz⟩, Prod.ext (e.time_preserving t z) rfl⟩
  have hs := e.smooth_inverse_on.comp
    (contMDiff_const.prodMk contMDiff_id).contMDiffOn hmaps
  exact (hs (f x) (mem_image_of_mem f hx)).snd.contMDiffAt
    ((e.spatialMap_isOpen_image hU ht).mem_nhds (mem_image_of_mem f hx))

def spatialHomeomorph (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : J ∈ 𝓝 t) :
    OpenPartialHomeomorph L.carrier.carrier M := by
  let f := fun x ↦ (e.toFun (t, x)).2
  let f' := fun y ↦ (e.inverse (t, y)).2
  have hleft (x : L.carrier.carrier) (hx : x ∈ U) : f' (f x) = x := by
    have hp : e.toFun (t, x) = (t, f x) := Prod.ext (e.time_preserving t x) rfl
    simpa only [hp] using congrArg Prod.snd
      (e.left_inverse (t, x) ⟨mem_of_mem_nhds ht, hx⟩)
  exact {
    toFun := f
    invFun := f'
    source := U
    target := f '' U
    map_source' := fun x hx ↦ mem_image_of_mem f hx
    map_target' := by rintro _ ⟨x, hx, rfl⟩; simpa only [hleft x hx] using hx
    left_inv' := hleft
    right_inv' := by rintro _ ⟨x, hx, rfl⟩; rw [hleft x hx]
    open_source := hU
    open_target := e.spatialMap_isOpen_image hU ht
    continuousOn_toFun := fun x hx ↦
      (e.spatialMap_contMDiffAt_of_time_nhds hU ht hx).continuousAt.continuousWithinAt
    continuousOn_invFun := by
      rintro _ ⟨x, hx, rfl⟩
      exact (e.spatialInverse_contMDiffAt hU ht hx).continuousAt.continuousWithinAt }

theorem spatialHomeomorph_mdifferentiable
    (e : AncientSpacetimeEmbedding (R := R) L (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : J ∈ 𝓝 t) :
    (e.spatialHomeomorph hU ht).MDifferentiable (𝓡 n) (𝓡 n) := by
  constructor
  · intro x hx
    exact (e.spatialMap_contMDiffAt_of_time_nhds hU ht hx).mdifferentiableAt (by simp)
      |>.mdifferentiableWithinAt
  · rintro _ ⟨x, hx, rfl⟩
    exact (e.spatialInverse_contMDiffAt hU ht hx).mdifferentiableAt (by simp)
      |>.mdifferentiableWithinAt

end AncientSpacetimeEmbedding
end PoincareConjecture
