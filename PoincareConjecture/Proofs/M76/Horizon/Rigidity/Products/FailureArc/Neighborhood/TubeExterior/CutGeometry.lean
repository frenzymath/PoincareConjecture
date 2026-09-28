import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Geometry



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem OriginalIntervalTube.interior_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    interior (R \ U.map '' openTube r) = interior R \ U.map '' closedTube r := by
  rw [sdiff_eq, interior_inter, interior_compl,
    OriginalIntervalTube.closure_openTube U hr hr1]
  rfl

theorem OriginalIntervalTube.closedTube_inter_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (U.map '' closedTube r) ∩ (R \ U.map '' openTube r) = U.map '' lateral r := by
  rw [← OriginalIntervalTube.closedTube_sdiff_openTube U hr hr1]
  ext x
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · rintro ⟨⟨z,hz,rfl⟩,hn⟩
    exact ⟨⟨z,hz,rfl⟩,U.mapsTo_region (closedTube_subset hr1 hz),hn⟩

theorem OriginalIntervalTube.closedTube_union_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr1 : r ≤ 1) :
    (U.map '' closedTube r) ∪ (R \ U.map '' openTube r) = R := by
  ext x
  constructor
  · rintro (⟨z,hz,rfl⟩ | hx)
    · exact U.mapsTo_region (closedTube_subset hr1 hz)
    · exact hx.1
  · intro hx
    by_cases h : x ∈ U.map '' openTube r
    · exact Or.inl (image_mono (openTube_subset r) h)
    · exact Or.inr ⟨hx,h⟩

theorem OriginalIntervalTube.frontier_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    frontier (R \ U.map '' openTube r) =
      (frontier R \ U.map '' openTube r) ∪ U.map '' lateral r := by
  rw [(OriginalIntervalTube.isCompact_exterior U hR he hr hr1).isClosed.frontier_eq,
    OriginalIntervalTube.interior_exterior U hr hr1,
    he.closed.frontier_eq,
    ← OriginalIntervalTube.closedTube_inter_exterior U hr hr1]
  ext x
  simp only [mem_sdiff,mem_union,mem_inter_iff]
  tauto

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
