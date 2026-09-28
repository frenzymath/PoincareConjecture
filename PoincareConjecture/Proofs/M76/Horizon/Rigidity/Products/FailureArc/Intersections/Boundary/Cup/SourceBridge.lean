import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Cup.Bridge



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_bridge_on_source_half
    {X ι E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {τ : C3 → X}
    (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    {c : P2 → E} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source) :
    ∃ g : E → X, PolyhedralPLInCharts e g (c '' halfSource false) ∧
      InjOn g (c '' halfSource false) ∧
      (∀ p ∈ halfSource false, g (c p) = τ (bridgeCoordinates p)) ∧
      g '' (c '' halfSource false) =
        τ '' ((Icc (-1 : ℝ) 1 ×ˢ {(1 : ℝ)}) ×ˢ Icc (0 : ℝ) 1) := by
  have hhalf := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 0 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hhalf
  have hKs' : K.space = halfSource false := hKs
  have hcHalf : FinitePiecewiseAffineOn c (halfSource false) := by
    rw [← hKs']
    exact hc.restrict K hK (hKs'.subset.trans (halfSource_subset_source false))
  obtain ⟨H, hH, hHval⟩ := hcHalf.exists_homeomorph_image (hci.mono (halfSource_subset_source false))
  obtain ⟨u, hu, huval⟩ := hH.symm
  have humap : MapsTo u (c '' halfSource false) (halfSource false) := by
    intro x hx
    rw [← huval ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  have huc (p : P2) (hp : p ∈ halfSource false) : u (c p) = p := by
    have hv := huval (H ⟨p, hp⟩)
    rw [H.symm_apply_apply] at hv
    simpa only [hHval] using hv.symm
  have hui : InjOn u (c '' halfSource false) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.symm.injective (Subtype.ext
      ((huval ⟨x, hx⟩).trans (hxy.trans (huval ⟨y, hy⟩).symm))))
  have hb : PolyhedralPLInCharts e (τ ∘ bridgeCoordinates) (halfSource false) := by
    rw [← hKs']
    exact hτ.comp_finitePiecewiseAffineOn K hK (hKs'.symm ▸ bridgeCoordinates_finitePL)
      (fun p hp ↦ bridgeCoordinates_mapsTo (hKs'.subset hp))
  let g : E → X := (τ ∘ bridgeCoordinates) ∘ u
  have hg : PolyhedralPLInCharts e g (c '' halfSource false) := by
    obtain ⟨L, hL, hLs, hLf⟩ := hu
    rw [← hLs]
    exact hb.comp_finitePiecewiseAffineOn L hL ⟨L, hL, rfl, hLf⟩
      (fun x hx ↦ humap (hLs.subset hx))
  have hgi : InjOn g (c '' halfSource false) :=
    (hτi.comp bridgeCoordinates_injective.injOn bridgeCoordinates_mapsTo).comp hui humap
  have hvalue (p : P2) (hp : p ∈ halfSource false) : g (c p) = τ (bridgeCoordinates p) := by
    simp only [g, Function.comp_apply, huc p hp]
  refine ⟨g, hg, hgi, hvalue, ?_⟩
  calc
    g '' (c '' halfSource false) = (g ∘ c) '' halfSource false := (image_comp _ _ _).symm
    _ = (τ ∘ bridgeCoordinates) '' halfSource false := image_congr hvalue
    _ = τ '' (bridgeCoordinates '' halfSource false) := image_comp _ _ _
    _ = _ := by rw [bridgeCoordinates_image]

end PoincareConjecture.M76.Dehn.Annuli.BoundaryCup
