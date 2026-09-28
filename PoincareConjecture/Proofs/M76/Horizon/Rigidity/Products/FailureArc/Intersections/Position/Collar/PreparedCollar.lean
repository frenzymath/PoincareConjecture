import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.ContactWindow
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.AnnulusCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.SubdivisionGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.CutCleanup
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.MarkedSubdivision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Frontier



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem OriginalSurfacePairChart.center_mem_frontier_of_region_halfspace
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T R : Set X} {y : X}
    (C : OriginalSurfacePairChart e S T y true)
    (hR : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔
      0 ≤ (C.coordinates z).1.2) : y ∈ frontier R := by
  have hh := (C.frontier_iff_of_region_halfspace hR (C.chart y) C.center_coordinates).mpr
    (by rw [C.center_zero]; rfl)
  simpa only [C.chart.left_inv C.center_source] using hh

theorem exists_prepared_original_annulus_collar
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Source K : SimplicialComplex ℝ V2) (hSource : Source.faces.Finite) (hK : K.faces.Finite)
    (hKs : K.space = Ann)
    {f g : V2 → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hg : PolyhedralPLInCharts e g K.space) (hfi : InjOn f Source.space) (hgi : InjOn g K.space)
    (R : Set X) (hgR : MapsTo g K.space R)
    (hproper : ∀ x ∈ K.space, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hboundary : ∀ x ∈ frontier Ann, g x ∈ f '' Source.space →
      ∃ C : OriginalSurfacePairChart e (f '' Source.space) (g '' K.space) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    {Z : Set X} (hZ : IsClosed Z) (hZT : Disjoint Z (g '' K.space)) :
    ∃ (c : ℝ) (N L : SimplicialComplex ℝ V2) (H : X ≃ₜ X),
      0 < c ∧ N.faces.Finite ∧ N.IsSubdivision K ∧ L ≤ N ∧
      L.space = Ann ∩ {x | planarAnnulusRimHeight x ≤ c} ∧ frontier Ann ⊆ L.space ∧
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      H ⁻¹' (g '' K.space) = g '' K.space ∧ H ⁻¹' R = R ∧ EqOn H id Z ∧
      Disjoint (H '' (f '' Source.space)) (g '' (N.vertices ∩ L.space)) ∧
      (∀ a ∈ N.faces, a.card = 2 →
        convexHull ℝ (a : Set V2) ⊆ Ann ∩ {x | planarAnnulusRimHeight x = c} →
        (H '' (f '' Source.space) ∩ (g '' convexHull ℝ (a : Set V2))).Finite ∧
          HasOriginalEdgeCofaceCharts e (H '' (f '' Source.space)) N g a) ∧
      (∀ p ∈ N.vertices, ∃ B : OpenPartialHomeomorph X V3,
        MapsTo g (N.closedStar p).space B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (N.closedStar p).AffineOnFaces (B ∘ g)) ∧
      (∀ s ∈ N.faces, s ∉ L.faces →
        ∃ (B : OpenPartialHomeomorph X V3) (A : V2 →ᴬ[ℝ] V3),
          (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
          Disjoint B.source (frontier R) ∧ MapsTo g (convexHull ℝ (s : Set V2)) B.source ∧
          EqOn (B ∘ g) A (convexHull ℝ (s : Set V2))) ∧
      (∀ x ∈ frontier Ann, g x ∈ H '' (f '' Source.space) →
        ∃ C : OriginalSurfacePairChart e (H '' (f '' Source.space)) (g '' K.space) (g x) true,
          ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
      ∀ x ∈ L.space, x ∈ interior Ann → g x ∈ H '' (f '' Source.space) →
        Nonempty (OriginalSurfacePairChart e (H '' (f '' Source.space)) (g '' K.space) (g x) false) := by
  classical
  have hcompact := K.isCompact_space_of_finite hK
  have hAnn : IsCompact Ann := hKs ▸ hcompact
  have hrimK : frontier Ann ⊆ K.space := hAnn.isClosed.frontier_subset.trans hKs.symm.subset
  have hclosed : IsClosed (f '' Source.space) :=
    ((Source.isCompact_space_of_finite hSource).image_of_continuousOn hf.continuousOn).isClosed
  obtain ⟨b, hb, _, hinterior⟩ := exists_thin_collar_interior_pair_charts
    hcompact hclosed hg.continuousOn hproper (by
      intro x hx hxf
      obtain ⟨C, hC⟩ := hboundary x hx.2 hxf
      exact ⟨C, C.frontier_iff_of_region_halfspace hC⟩)
    continuous_planarAnnulusRimHeight.continuousOn
    (fun x hx => planarAnnulusRimHeight_nonneg (hKs.subset hx))
    (fun x hx => planarAnnulusRimHeight_eq_zero_iff (hKs.subset hx)) zero_lt_one
  obtain ⟨c, J, M, hc, hcb, hJ, hJK, hJs, hMJ, hM, hMs, hrimM, hfull,
      hfinite, hstars, hfaces⟩ :=
    exists_regular_planar_annulus_collar_charts he Source K hSource hK hKs hf hg hfi hgi
      (frontier R) isClosed_frontier (fun x hx => (hproper x hx).mp)
      (fun x hx hxf => ⟨(hboundary x hx hxf).choose⟩) hb
  obtain ⟨W₀, hW₀, hsmallW₀, hcutW₀, hwindow₀⟩ := exists_open_collar_contact_window
    hcompact hg.continuousOn hgi hgR hproper continuous_planarAnnulusRimHeight hc hcb
    (fun x hx => planarAnnulusRimHeight_eq_zero_iff (hKs.subset hx))
    (fun x hx => hboundary x hx.2) hinterior
  let W := W₀ ∩ Zᶜ
  have hW : IsOpen W := hW₀.inter hZ.isOpen_compl
  have htargetZ : g '' K.space ⊆ Zᶜ := fun y hy hz => disjoint_left.mp hZT hz hy
  have hsmallW : g '' (K.space ∩ {x | planarAnnulusRimHeight x ≤ c}) ⊆ W :=
    fun y hy => ⟨hsmallW₀ hy, htargetZ (image_mono inter_subset_left hy)⟩
  have hcutW : g '' (K.space ∩ {x | planarAnnulusRimHeight x = c}) ⊆ W ∩ interior R :=
    fun y hy => ⟨⟨(hcutW₀ hy).1, htargetZ (image_mono inter_subset_left hy)⟩, (hcutW₀ hy).2⟩
  have hwindow := fun y hyS hyT (hyW : y ∈ W) => hwindow₀ y hyS hyT hyW.1
  let P := Ann ∩ {x | planarAnnulusRimHeight x = c}
  have hP : IsClosed P := hAnn.isClosed.inter
    (isClosed_eq continuous_planarAnnulusRimHeight continuous_const)
  have hPJ : P ⊆ J.space := inter_subset_left.trans hJs.symm.subset
  have hPK : P ⊆ K.space := inter_subset_left.trans hKs.symm.subset
  have hQW : g '' M.space ⊆ W := by simpa only [hMs, hKs] using hsmallW
  have hPU : g '' P ⊆ W ∩ interior R := by simpa only [P, hKs] using hcutW
  have hfiniteP : (P ∩ g ⁻¹' (f '' Source.space)).Finite := by
    convert hfinite using 1
    ext x
    simp only [P, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    tauto
  have hcut : ∀ x ∈ P, g x ∈ f '' Source.space →
      Nonempty (OriginalSurfacePairChart e (f '' Source.space) (g '' K.space) (g x) false) := by
    intro x hx hxf
    apply hinterior x (hPK hx) (by rw [hx.2]; exact hcb.le) _ hxf
    intro hxr
    exact hc.ne' (hx.2.symm.trans ((planarAnnulusRimHeight_eq_zero_iff hx.1).mpr hxr))
  obtain ⟨N, H, B, hN, hNJ, hB, hBW, hHoff, hHPL, hHinv, hHT, hHR, hHV, hHE⟩ :=
    exists_original_collar_vertex_cut_position hcover he J hJ
      (hJK.space_eq.symm ▸ hg) (hJK.space_eq.symm ▸ hgi)
      (by rw [hJK.space_eq])
      P M.space hP hPJ (by rw [hMs, hJs]; exact inter_subset_left)
      hfiniteP hcut (hW.inter isOpen_interior) inter_subset_right
      ((image_mono inter_subset_left).trans hPU) hW hQW (by
        intro y hyS hyT hy
        apply hwindow y hyS hyT
        rcases hy with hy | hy
        · exact hy.1
        · exact hQW hy)
  have hBW' : B ⊆ W := hBW.trans (union_subset inter_subset_left (Subset.refl _))
  obtain ⟨L, hLN, hL, hLs, _⟩ :=
    CollarMesh.exists_full_subcomplex_of_subdivision J M N hMJ hfull hN hNJ
  have hNK := hNJ.trans hJK
  have hcurrent (x : V2) (hx : x ∈ M.space) (hxf : g x ∈ H '' (f '' Source.space)) :
      (g x ∈ interior R ∧ Nonempty
        (OriginalSurfacePairChart e (H '' (f '' Source.space)) (g '' K.space) (g x) false)) ∨
      ∃ C : OriginalSurfacePairChart e (H '' (f '' Source.space)) (g '' K.space) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2 := by
    obtain ⟨y, hyS, hyeq⟩ := hxf
    have hyT : y ∈ g '' K.space := hHT.subset (by
      change H y ∈ g '' K.space
      rw [hyeq]
      exact mem_image_of_mem g (hKs.symm.subset (hMs.subset hx).1))
    have hyW : y ∈ W := by
      by_contra hn
      have hfix := hHoff (fun hyB => hn (hBW' hyB))
      have hxy : g x = y := hyeq.symm.trans hfix
      exact hn (hxy ▸ hQW (mem_image_of_mem g hx))
    have hh := region_pair_chart_image_of_preserving_sets hcover H hHinv hHT hHR
      (hwindow y hyS hyT hyW)
    rwa [hyeq] at hh
  refine ⟨c, N, L, H, hc, hN, hNK, hLN, hLs.trans hMs,
    hrimM.trans hLs.symm.subset, hHPL, hHinv, hHT, hHR, ?_, ?_, hHE,
    subdivision_preserves_original_chart_stars J N hJ hNJ g hstars,
    subdivision_preserves_active_original_charts J M N L hNJ hLN hLs hfaces, ?_, ?_⟩
  · intro y hy
    exact hHoff (fun hyB => (hBW' hyB).2 hy)
  · simpa only [hLs] using hHV
  · intro x hx hxf
    rcases hcurrent x (hrimM hx) hxf with hh | hh
    · exact False.elim (disjoint_left.mp disjoint_interior_frontier hh.1
        ((hproper x (hrimK hx)).mpr hx))
    · exact hh
  · intro x hx hxint hxf
    rcases hcurrent x (hLs.subset hx) hxf with hh | ⟨C, hC⟩
    · exact hh.2
    · exact False.elim (disjoint_left.mp disjoint_interior_frontier hxint
        ((hproper x (hKs.symm.subset (hMs.subset (hLs.subset hx)).1)).mp
          (C.center_mem_frontier_of_region_halfspace hC)))

end PoincareConjecture.M76
