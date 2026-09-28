import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Restriction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.RelativeFrontierOpenness
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeRegionClosure

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem OriginalIntervalTube.exists_closedTube_ball
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Nonempty (ChartwisePLBall e (U.map '' closedTube r)
      (U.map '' lateral r ∪ U.map '' ends r)) := by
  obtain ⟨hpl, hi, _⟩ := OriginalIntervalTube.restrict_closedTube U hr hr1
  have h := exists_chartwisePLBall_image (isFinitePLBallPair_closedTube hr)
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : C3 ≃L[ℝ] V3)
    hpl Subset.rfl hi
  simpa only [image_union] using h

theorem OriginalIntervalTube.closedTube_inter_frontier
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr1 : r ≤ 1) :
    (U.map '' closedTube r) ∩ frontier R = U.map '' ends r := by
  ext x
  constructor
  · rintro ⟨⟨z,hz,rfl⟩,hf⟩
    exact ⟨z,⟨hz.1,(U.frontier_iff z (closedTube_subset hr1 hz)).mp hf⟩,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,ends_subset hz,rfl⟩,
      (U.frontier_iff z (closedTube_subset hr1 (ends_subset hz))).mpr hz.2⟩

theorem OriginalIntervalTube.closedTube_sdiff_lateral
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (U.map '' closedTube r) \ (U.map '' lateral r) = U.map '' openTube r := by
  have hi := (OriginalIntervalTube.restrict_closedTube U hr hr1).2.1
  rw [← TubeExterior.closedTube_sdiff_lateral r]
  simpa only [inter_eq_right.mpr (lateral_subset r)] using
    (hi.image_sdiff (t := lateral r)).symm

theorem OriginalIntervalTube.isOpen_relative_openTube
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (he : PLDomain e R) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    IsOpen ((Subtype.val : R → X) ⁻¹' (U.map '' openTube r)) := by
  obtain ⟨b⟩ := OriginalIntervalTube.exists_closedTube_ball U hr hr1
  have hc := (OriginalIntervalTube.restrict_closedTube U hr hr1).1.continuousOn
  have hlat : IsCompact (U.map '' lateral r) :=
    (isCompact_lateral r).image_of_continuousOn (hc.mono (lateral_subset r))
  have hBR : U.map '' closedTube r ⊆ R := by
    rintro _ ⟨z,hz,rfl⟩
    exact U.mapsTo_region (closedTube_subset hr1 hz)
  have hfront : frontier (U.map '' closedTube r) ⊆
      frontier R ∪ U.map '' lateral r := by
    rw [b.frontier_eq]
    rintro x (hx | hx)
    · exact Or.inr hx
    · exact Or.inl ((OriginalIntervalTube.closedTube_inter_frontier U hr1).symm.subset hx).2
  have h := he.isOpen_relative_sdiff_of_frontier_subset b.closure_interior
    hBR hlat.isClosed hfront
  rwa [OriginalIntervalTube.closedTube_sdiff_lateral U hr hr1] at h

theorem OriginalIntervalTube.isCompact_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    IsCompact (R \ U.map '' openTube r) := by
  obtain ⟨V,hV,hVe⟩ := isOpen_induced_iff.mp
    (OriginalIntervalTube.isOpen_relative_openTube U he hr hr1)
  have hset : R \ U.map '' openTube r = R \ V := by
    ext x
    constructor
    · rintro ⟨hx,hn⟩
      exact ⟨hx,fun hv => hn ((Set.ext_iff.mp hVe ⟨x,hx⟩).mp hv)⟩
    · rintro ⟨hx,hn⟩
      exact ⟨hx,fun hv => hn ((Set.ext_iff.mp hVe ⟨x,hx⟩).mpr hv)⟩
  rw [hset]
  exact hR.diff hV

theorem OriginalIntervalTube.closedTube_sdiff_openTube
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (U.map '' closedTube r) \ (U.map '' openTube r) = U.map '' lateral r := by
  have hi := (OriginalIntervalTube.restrict_closedTube U hr hr1).2.1
  rw [← TubeExterior.closedTube_sdiff_openTube r]
  simpa only [inter_eq_right.mpr (openTube_subset r)] using
    (hi.image_sdiff (t := openTube r)).symm

theorem OriginalIntervalTube.closure_openTube
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    closure (U.map '' openTube r) = U.map '' closedTube r := by
  obtain ⟨b⟩ := OriginalIntervalTube.exists_closedTube_ball U hr hr1
  have hc : IsClosed (U.map '' closedTube r) :=
    ((isCompact_closedTube r).image_of_continuousOn
      (OriginalIntervalTube.restrict_closedTube U hr hr1).1.continuousOn).isClosed
  have hsub : interior (U.map '' closedTube r) ⊆ U.map '' openTube r := by
    rw [← OriginalIntervalTube.closedTube_sdiff_lateral U hr hr1]
    intro x hx
    refine ⟨interior_subset hx, ?_⟩
    intro hz
    exact (b.frontier_eq.symm.subset (Or.inl hz)).2 hx
  apply Subset.antisymm
  · exact closure_minimal (image_mono (openTube_subset r)) hc
  · rw [← b.closure_interior]
    exact closure_mono hsub

theorem OriginalIntervalTube.relative_regular_closed_closedTube
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    closure (interior ((Subtype.val : R → X) ⁻¹' (U.map '' closedTube r))) =
      (Subtype.val : R → X) ⁻¹' (U.map '' closedTube r) := by
  obtain ⟨b⟩ := OriginalIntervalTube.exists_closedTube_ball U hr hr1
  have h := OriginalIntervalTube.restrict_closedTube U hr hr1
  apply regular_closed_subtype_preimage
    ((isCompact_closedTube r).image_of_continuousOn h.1.continuousOn).isClosed
    _ b.closure_interior
  rintro _ ⟨z,hz,rfl⟩
  exact h.2.2.1 hz

theorem OriginalIntervalTube.relative_frontier_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (he : PLDomain e R) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    frontier ((Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r)) =
      (Subtype.val : R → X) ⁻¹' (U.map '' lateral r) := by
  have hUR : U.map '' openTube r ⊆ R := by
    rintro _ ⟨z,hz,rfl⟩
    exact U.mapsTo_region (closedTube_subset hr1 (openTube_subset r hz))
  rw [frontier_subtype_cut_of_closure hUR
    (OriginalIntervalTube.isOpen_relative_openTube U he hr hr1)
    (OriginalIntervalTube.closure_openTube U hr hr1),
    OriginalIntervalTube.closedTube_sdiff_openTube U hr hr1]

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
