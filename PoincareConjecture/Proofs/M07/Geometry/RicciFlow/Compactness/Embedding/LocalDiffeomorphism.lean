import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.SpatialRegularity








set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SmoothSpacetimeEmbedding

variable {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
  {F : BasedFlow n T' T C} {G : BasedFlow n T' T D} {U : Set C.carrier}

theorem spatialMap_isOpen_image
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T) :
    @IsOpen D.carrier D.topologicalSpace ((fun y ↦ (e.toFun (t, y)).2) '' U) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    (e.spatialMap_contMDiffAt hU ht hx) (e.spatialMap_mfderiv_bijective hU ht hx)]
  exact image_mem_map (hU.mem_nhds hx)

theorem spatialInverse_contMDiffAt
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T)
    {x : C.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun y ↦ (e.inverse (t, y)).2)
      (e.toFun (t, x)).2 := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let f : C.carrier → D.carrier := fun y ↦ (e.toFun (t, y)).2
  have hmaps : MapsTo (fun y : D.carrier ↦ (t, y)) (f '' U)
      (e.toFun '' (Ioo T' T ×ˢ U)) := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨(t, z), ⟨ht, hz⟩, Prod.ext (e.time_preserving t z) rfl⟩
  have hs := e.smooth_inverse_on.comp
    (contMDiff_const.prodMk contMDiff_id).contMDiffOn hmaps
  exact (hs (f x) (mem_image_of_mem f hx)).snd.contMDiffAt
    ((e.spatialMap_isOpen_image hU ht).mem_nhds (mem_image_of_mem f hx))

end PoincareConjecture.SmoothSpacetimeEmbedding
