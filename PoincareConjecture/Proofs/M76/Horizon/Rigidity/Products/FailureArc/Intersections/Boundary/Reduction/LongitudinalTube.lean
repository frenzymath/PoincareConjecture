import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.OriginalTube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Longitudinal



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

def OriginalIntervalTube.longitudinalReverse
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f g : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f g) :
    OriginalIntervalTube e R W S T C D f g := by
  let hs : source ≃ₜ source := {
    toFun := fun p ↦ ⟨spanningSourceReverse p, spanningSourceReverse_mapsTo p.property⟩
    invFun := fun p ↦ ⟨spanningSourceReverse p, spanningSourceReverse_mapsTo p.property⟩
    left_inv := fun p ↦ Subtype.ext (spanningSourceReverse_involutive p)
    right_inv := fun p ↦ Subtype.ext (spanningSourceReverse_involutive p)
    continuous_toFun := (spanningSourceReverse.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (spanningSourceReverse.continuous.comp continuous_subtype_val).subtype_mk _ }
  let ht : tube ≃ₜ tube := {
    toFun := fun p ↦ ⟨spanningTubeReverse p, spanningTubeReverse_mapsTo p.property⟩
    invFun := fun p ↦ ⟨spanningTubeReverse p, spanningTubeReverse_mapsTo p.property⟩
    left_inv := fun p ↦ Subtype.ext (spanningTubeReverse_involutive p)
    right_inv := fun p ↦ Subtype.ext (spanningTubeReverse_involutive p)
    continuous_toFun := (spanningTubeReverse.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (spanningTubeReverse.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine {
    first := U.first ∘ spanningSourceReverse
    second := U.second ∘ spanningSourceReverse
    map := U.map ∘ spanningTubeReverse
    first_pl := U.first_pl.comp spanningSourceReverse_finitePL spanningSourceReverse_mapsTo
    second_pl := U.second_pl.comp spanningSourceReverse_finitePL spanningSourceReverse_mapsTo
    first_embedding := U.first_embedding.comp hs.isEmbedding
    second_embedding := U.second_embedding.comp hs.isEmbedding
    first_mapsTo := U.first_mapsTo.comp spanningSourceReverse_mapsTo
    second_mapsTo := U.second_mapsTo.comp spanningSourceReverse_mapsTo
    pl := spanningTubeReverse_polyhedralPL U.pl
    embedding := U.embedding.comp ht.isEmbedding
    mapsTo_region := U.mapsTo_region.comp spanningTubeReverse_mapsTo
    mapsTo_neighborhood := U.mapsTo_neighborhood.comp spanningTubeReverse_mapsTo
    first_sheet := fun p hp ↦ U.first_sheet _ (spanningSourceReverse_mapsTo hp)
    second_sheet := fun p hp ↦ U.second_sheet _ (spanningSourceReverse_mapsTo hp)
    first_preimage := ?_
    second_preimage := ?_
    first_center := ?_
    second_center := ?_
    first_trace := fun z hz ↦ U.first_trace _ (spanningTubeReverse_mapsTo hz)
    second_trace := fun z hz ↦ U.second_trace _ (spanningTubeReverse_mapsTo hz)
    frontier_iff := ?_ }
  · rw [image_comp, spanningTubeReverse_image, image_comp, spanningSourceReverse_image]
    exact U.first_preimage
  · rw [image_comp, spanningTubeReverse_image, image_comp, spanningSourceReverse_image]
    exact U.second_preimage
  · rw [image_comp, spanningSourceReverse_arm_image]
    exact U.first_center
  · rw [image_comp, spanningSourceReverse_arm_image]
    exact U.second_center
  · intro z hz
    change U.map (spanningTubeReverse z) ∈ frontier R ↔ _
    rw [U.frontier_iff _ (spanningTubeReverse_mapsTo hz), spanningTubeReverse_apply]
    dsimp only
    constructor <;> rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

end PoincareConjecture.M76.Dehn.Annuli
