import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.LateralPatch
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.LocalDiskChart

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1

theorem OriginalIntervalTube.exists_lateral_pair_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {z : C3} (hz : z ∈ lateral r) :
    ∃ H : OpenPartialHomeomorph X C3,
      U.map z ∈ H.source ∧ H.target = interior (CoordinateHalfBoxes.box 1) ∧
      H (U.map z) = 0 ∧
      (∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source) ∧
      ((H.source ⊆ interior R ∧
        ∀ x ∈ H.source, x ∈ U.map '' lateral r ↔ (H x).2 = 0) ∨
       ((∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1) ∧
        ∀ x ∈ H.source, x ∈ U.map '' lateral r ↔
          0 ≤ (H x).1.1 ∧ (H x).2 = 0)) := by
  obtain ⟨P, Q, V, hP, hPlat, hV, hzV, hlocal, hboundary⟩ :=
    exists_lateral_disk_patch hr hz
  have hPtube : P ⊆ tube := hPlat.trans ((lateral_subset r).trans (closedTube_subset hr1))
  have hztube : z ∈ tube := closedTube_subset hr1 (lateral_subset r hz)
  have hzP : z ∈ P := (hlocal z hzV).mp hz
  obtain ⟨O, hO, hOeq⟩ := U.embedding.isInducing.isOpen_iff.mp
    (hV.preimage (continuous_subtype_val : Continuous (Subtype.val : tube → C3)))
  have hOmem (w : C3) (hw : w ∈ tube) : U.map w ∈ O ↔ w ∈ V :=
    Set.ext_iff.mp hOeq ⟨w, hw⟩
  have hlocalImage (x : X) (hx : x ∈ O) :
      x ∈ U.map '' lateral r ↔ x ∈ U.map '' P := by
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, (hlocal w ((hOmem w (closedTube_subset hr1 (lateral_subset r hw))).mp hx)).mp hw, rfl⟩
    · exact fun hxP => image_mono hPlat hxP
  obtain ⟨H, hH, hHboundary⟩ := hP.exists_cube_chart
    (ContinuousLinearEquiv.ofFinrankEq (by simp) : P2 ≃L[ℝ] V2)
  obtain ⟨g, hg, hgval⟩ := hH.symm
  have hgP : MapsTo g Disk P := by
    intro x hx
    rw [← hgval ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  have hgi : InjOn g Disk := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.symm.injective (Subtype.ext
      ((hgval ⟨x, hx⟩).trans (hxy.trans (hgval ⟨y, hy⟩).symm))))
  have hgimage : g '' Disk = P := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hgP hx
    · intro w hw
      refine ⟨H ⟨w, hw⟩, (H ⟨w, hw⟩).property, ?_⟩
      rw [← hgval, H.symm_apply_apply]
  have hgr (x : Disk) : g x ∈ Q ↔ (x : V2) ∈ sphere 0 1 := by
    rw [← hgval x, hHboundary, H.apply_symm_apply, frontier_closedBall _ one_ne_zero]
  have hj : PolyhedralPLInCharts e (U.map ∘ g) Disk := by
    obtain ⟨K, hK, hKs, hKf⟩ := hg
    rw [← hKs]
    exact U.pl.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hKf⟩
      (fun _ hx => hPtube (hgP (hKs.subset hx)))
  have huinj : InjOn U.map tube := fun x hx y hy hxy =>
    congrArg Subtype.val (U.embedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hji : InjOn (U.map ∘ g) Disk := huinj.comp hgi (fun _ hx => hPtube (hgP hx))
  have hjemb : IsEmbedding (fun x : Disk => (U.map ∘ g) x) :=
    (hj.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hji x.property y.property hxy))).isEmbedding
  have hjR : MapsTo (U.map ∘ g) Disk R := fun _ hx => U.mapsTo_region (hPtube (hgP hx))
  have hjproper (x : Disk) (hx : (U.map ∘ g) x ∈ O) :
      (U.map ∘ g) x ∈ frontier R ↔ (x : V2) ∈ sphere 0 1 := by
    exact (U.frontier_iff (g x) (hPtube (hgP x.property))).trans
      ((hboundary (g x) (hgP x.property) ((hOmem _ (hPtube (hgP x.property))).mp hx)).symm.trans
        (hgr x))
  let w : Disk := H ⟨z, hzP⟩
  have hw : (U.map ∘ g) w = U.map z := by
    change U.map (g (H ⟨z, hzP⟩)) = _
    rw [← hgval, H.symm_apply_apply]
  obtain ⟨B, hwB, hBO, hBt, hBw, hBcompat, hpair⟩ :=
    exists_original_locally_proper_disk_pair_chart he hj hjemb hjR hO hjproper
      w (hw.symm ▸ (hOmem z hztube).mpr hzV)
  have himage : (U.map ∘ g) '' Disk = U.map '' P := by rw [image_comp, hgimage]
  refine ⟨B, hw ▸ hwB, hBt, hw ▸ hBw, hBcompat, ?_⟩
  rcases hpair with ⟨hinside, hplane⟩ | ⟨hregion, hplane⟩
  · exact Or.inl ⟨hinside, fun x hx => (hlocalImage x (hBO hx)).trans
      (himage ▸ hplane x hx)⟩
  · exact Or.inr ⟨hregion, fun x hx => (hlocalImage x (hBO hx)).trans
      (himage ▸ hplane x hx)⟩

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
