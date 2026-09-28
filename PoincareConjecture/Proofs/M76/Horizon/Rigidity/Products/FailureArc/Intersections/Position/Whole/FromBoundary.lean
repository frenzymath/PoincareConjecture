import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.PreparedCollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.WholeFromProtected
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.InteriorAnchor



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_annulus_position_of_boundary_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Source K : SimplicialComplex ℝ V2) (hSource : Source.faces.Finite) (hK : K.faces.Finite)
    (hKs : K.space = Ann)
    {f g : V2 → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hg : PolyhedralPLInCharts e g K.space) (hfi : InjOn f Source.space) (hgi : InjOn g K.space)
    (R : Set X) (hfR : MapsTo f Source.space R) (hgR : MapsTo g K.space R)
    (hfp : ∀ x ∈ Source.space, f x ∈ frontier R ↔ x ∈ frontier Source.space)
    (hgp : ∀ x ∈ K.space, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hconnected : IsPreconnected (Source.space \ frontier Source.space))
    (hboundary : ∀ x ∈ frontier Ann, g x ∈ f '' Source.space →
      ∃ C : OriginalSurfacePairChart e (f '' Source.space) (g '' K.space) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    (hpoint : ((f '' Source.space) ∩ (g '' frontier Ann)).Nonempty)
    {Z : Set X} (hZ : IsClosed Z) (hZT : Disjoint Z (g '' K.space)) :
    ∃ (H : X ≃ₜ X) (k : V2 → X),
      PolyhedralPLInCharts e k Source.space ∧ InjOn k Source.space ∧ MapsTo k Source.space R ∧
      (∀ x ∈ Source.space, k x ∈ frontier R ↔ x ∈ frontier Source.space) ∧
      EqOn k (H ∘ f) (Source.space ∩ frontier Source.space) ∧
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      H ⁻¹' (g '' K.space) = g '' K.space ∧ H ⁻¹' R = R ∧ EqOn H id Z ∧
      (∀ x ∈ frontier Ann, g x ∈ k '' Source.space →
        ∃ C : OriginalSurfacePairChart e (k '' Source.space) (g '' K.space) (g x) true,
          ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
      (∀ x ∈ interior Ann, g x ∈ k '' Source.space →
        Nonempty (OriginalSurfacePairChart e (k '' Source.space) (g '' K.space) (g x) false)) ∧
      Nonempty (SurfaceIntersectionComponents Source.space Ann k g (frontier Ann)) := by
  classical
  have hAnn : IsCompact Ann := hKs ▸ K.isCompact_space_of_finite hK
  have hrimK : frontier Ann ⊆ K.space := hAnn.isClosed.frontier_subset.trans hKs.symm.subset
  obtain ⟨c, N, L, H, hc, hN, hNK, hLN, hLs, hrimL, hHPL, hHinv, hHT, hHR,
      hHZ, hvertices, hcut, hstars, hactive, hboundaryH, hcollarH⟩ :=
    exists_prepared_original_annulus_collar hcover he Source K hSource hK hKs hf hg hfi hgi
      R hgR hgp hboundary hZ hZT
  have hNs := hNK.space_eq.trans hKs
  have hHfront : H ⁻¹' frontier R = frontier R := by rw [H.preimage_frontier, hHR]
  have hfH := hf.comp_chart_homeomorph Source hSource H hcover hHPL
  have hfHi : InjOn (H ∘ f) Source.space := fun x hx y hy hh => hfi hx hy (H.injective hh)
  have hfHR : MapsTo (H ∘ f) Source.space R := fun x hx => hHR.symm.subset (hfR hx)
  have hfpH : ∀ x ∈ Source.space, (H ∘ f) x ∈ frontier R ↔ x ∈ frontier Source.space := by
    intro x hx
    exact (Set.ext_iff.mp hHfront (f x)).trans (hfp x hx)
  have himage : (H ∘ f) '' Source.space = H '' (f '' Source.space) :=
    (image_image H f Source.space).symm
  have hrimH : ∀ x ∈ Source.space, x ∉ interior Source.space → (H ∘ f) x ∈ frontier R := by
    intro x hx hxn
    exact (hfpH x hx).mpr ⟨subset_closure hx, hxn⟩
  have hboundaryN : ∀ x ∈ N.space \ interior N.space, g x ∈ (H ∘ f) '' Source.space →
      ∃ C : OriginalSurfacePairChart e ((H ∘ f) '' Source.space) (g '' N.space) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2 := by
    intro x hx hxf
    have hxrim : x ∈ frontier Ann := by
      rw [← hNs, (N.isCompact_space_of_finite hN).isClosed.frontier_eq]
      exact hx
    rw [himage, hNK.space_eq]
    exact hboundaryH x hxrim (himage.subset hxf)
  obtain ⟨F, W, hW, hfix, hLW, hFfront, hFPL, hFinv, hk, hki, _, hboundaryF,
      hinteriorF, hcomponents⟩ :=
    exists_whole_planar_position_from_protected_collar Source N L hSource hN hLN hNs
      hfH hfHi (hNK.space_eq.symm ▸ hg) (hNK.space_eq.symm ▸ hgi) hcover he hrimH
      (fun x hx => hgp x (hNK.space_eq.subset hx)) hc.le (by rw [hNs]; exact hLs)
      (by simpa only [himage] using hvertices) hstars hactive (by
        intro a ha ha2 haP
        simpa only [himage] using hcut a ha ha2 (by
          intro z hz
          exact ⟨hNs.subset (haP hz).1, (haP hz).2⟩))
      hboundaryN (by
        intro x hx hxint hxf
        simpa only [himage, hNK.space_eq] using
          hcollarH x hx (hNs ▸ hxint) (himage.subset hxf))
  obtain ⟨p, hpS, x, hxrim, hxp⟩ := hpoint
  have hpfront : p ∈ frontier R := hxp ▸ (hgp x (hrimK hxrim)).mpr hxrim
  have hHpT : H p ∈ g '' K.space := hHT.symm.subset
    (hxp ▸ mem_image_of_mem g (hrimK hxrim))
  obtain ⟨y, hyK, hyHp⟩ := hHpT
  have hyfront : g y ∈ frontier R := hyHp.symm ▸ hHfront.symm.subset hpfront
  have hyrim := (hgp y hyK).mp hyfront
  have hyS : g y ∈ H '' (f '' Source.space) := hyHp.symm ▸ mem_image_of_mem H hpS
  obtain ⟨C, hC⟩ := hboundaryN y (by
    rw [hNs, ← hAnn.isClosed.frontier_eq]
    exact hyrim) (himage.symm.subset hyS)
  obtain ⟨hkR, hkp, hkrim, _⟩ := proper_map_preserved_of_fixed_boundary_pair
    hfH.continuousOn hfHR hfpH hconnected C hC F hFfront hW
      (hLW (mem_image_of_mem g (hrimL hyrim))) hfix
  refine ⟨H, F ∘ (H ∘ f), hk, hki, hkR, hkp, hkrim, hHPL, hHinv, hHT, hHR,
    hHZ, ?_, ?_, ?_⟩
  · intro z hz hzf
    have hzN : z ∈ N.space \ interior N.space := by
      rw [hNs, ← hAnn.isClosed.frontier_eq]
      exact hz
    rw [← hNK.space_eq]
    exact hboundaryF z hzN hzf
  · intro z hz hzf
    simpa only [hNK.space_eq] using hinteriorF z (hNs.symm ▸ hz) hzf
  · simpa only [hNs, ← hAnn.isClosed.frontier_eq] using hcomponents

end PoincareConjecture.M76
