import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.ExteriorDensity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CutGeometry



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem OriginalIntervalTube.relative_regular_closed_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    closure (interior ((Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r))) =
      (Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r) :=
  regular_closed_subtype_preimage
    (OriginalIntervalTube.isCompact_exterior U hR he hr hr1.le).isClosed sdiff_subset
    (OriginalIntervalTube.closure_interior_exterior U hR he hr hr1)

theorem OriginalIntervalTube.relative_interior_closedTube
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    interior ((Subtype.val : R → X) ⁻¹' (U.map '' closedTube r)) =
      (Subtype.val : R → X) ⁻¹' (U.map '' openTube r) := by
  have hUR : U.map '' openTube r ⊆ R := by
    rintro _ ⟨z,hz,rfl⟩
    exact U.mapsTo_region (closedTube_subset hr1.le (openTube_subset r hz))
  have hclosure : closure ((Subtype.val : R → X) ⁻¹' (U.map '' openTube r)) =
      (Subtype.val : R → X) ⁻¹' (U.map '' closedTube r) := by
    rw [closure_subtype_preimage_of_subset hUR,
      OriginalIntervalTube.closure_openTube U hr hr1.le]
  have hcut : (Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r) =
      ((Subtype.val : R → X) ⁻¹' (U.map '' openTube r))ᶜ := by
    ext x
    exact and_iff_right x.property
  have hreg := OriginalIntervalTube.relative_regular_closed_exterior U hR he hr hr1
  rw [hcut,interior_compl,closure_compl,hclosure] at hreg
  exact compl_injective hreg

theorem OriginalIntervalTube.relative_frontier_closedTube
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    frontier ((Subtype.val : R → X) ⁻¹' (U.map '' closedTube r)) =
      (Subtype.val : R → X) ⁻¹' (U.map '' lateral r) := by
  have hc : IsClosed ((Subtype.val : R → X) ⁻¹' (U.map '' closedTube r)) :=
    ((isCompact_closedTube r).image_of_continuousOn
      (OriginalIntervalTube.restrict_closedTube U hr hr1.le).1.continuousOn).isClosed.preimage
      continuous_subtype_val
  rw [hc.frontier_eq,OriginalIntervalTube.relative_interior_closedTube U hR he hr hr1,
    ← preimage_sdiff,OriginalIntervalTube.closedTube_sdiff_openTube U hr hr1.le]

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
