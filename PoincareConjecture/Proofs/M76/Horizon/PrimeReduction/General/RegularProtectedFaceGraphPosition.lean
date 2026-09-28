import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.ProtectedFaceGraphPosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ProtectedSurfaceDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FaceAffineSignClosure
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.RelativeInteriorHeightSigns











set_option autoImplicit false

open Set Geometry Filter Module
open scoped Topology

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)




theorem exists_signed_regular_protected_face_graph_position
    (J P T : SimplicialComplex ℝ V3)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hPJ : P.space ⊆ J.space)
    (hcard : ∀ s ∈ P.faces, s.card ≤ 3)
    (hvertices : Disjoint P.space T.vertices)
    (hedges : ∀ a ∈ T.faces, a.card = 2 →
      (P.space ∩ convexHull ℝ (a : Set V3)).Finite)
    {t : Finset V3} (ht : t ∈ T.faces) (ht3 : t.card = 3)
    (htJ : convexHull ℝ (t : Set V3) ⊆ interior J.space)
    {Z : Set V3} (hZ : IsClosed Z) (hfront : frontier J.space ⊆ Z)
    {Ω : Set V3} (hΩ : IsOpen Ω)
    (hZΩ : P.space ∩ Z ∩ convexHull ℝ (t : Set V3) ⊆ Ω)
    (height : V3 →ᵃ[ℝ] ℝ)
    (hheight : ∀ x, height x = 0 ↔ x ∈ affineSpan ℝ (t : Set V3))
    (hlocal : ∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set V3),
      ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ V3),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set V3) ∩ U, ∃ L ∈ Q, y ∈ L)
    (hdisks : ∀ w ∈ P.space, w ∈ interior J.space →
      ∃ d rim : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d rim ∧ d ⊆ P.space ∧
        w ∈ d \ rim ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ rim)))
    (hregular : ∀ w ∈ (P.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) ∩ Ω,
      (∃ u v : V3, u ≠ w ∧ v ≠ w ∧ segment ℝ w u ∩ segment ℝ w v ⊆ {w} ∧
        ∀ᶠ x in 𝓝 w, x ∈ P.space ∩ {x | height x = 0} ↔
          x ∈ segment ℝ w u ∪ segment ℝ w v) ∧
      w ∈ closure (P.space ∩ {x | height x < 0}) ∧
      w ∈ closure (P.space ∩ {x | 0 < height x}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P₀ : SimplicialComplex ℝ V3) (H : PLCarrierMotion J.space P₀.space ε)
      (A G : SimplicialComplex ℝ V3) (W : Set V3),
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧
      (∀ a ∈ A.faces, a.card ≤ 3) ∧
      G.faces.Finite ∧ G.space = A.space ∩ convexHull ℝ (t : Set V3) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      IsOpen W ∧ Z ⊆ W ∧
      (∀ τ, EqOn (H.map τ) id W) ∧
      (∀ τ, H.map τ '' P.space ∩ W = P.space ∩ W) ∧
      Disjoint A.space T.vertices ∧
      (∀ a ∈ T.faces, a.card ≤ 2 →
        (A.space ∩ convexHull ℝ (a : Set V3)).Finite) ∧
      (∀ a ∈ A.faces,
        convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
              (convexHull ℝ (t : Set V3))) ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)) →
          (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      ∀ w ∈ A.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)),
        w ∈ closure (A.space ∩ {x | height x < 0}) ∧
          w ∈ closure (A.space ∩ {x | 0 < height x}) := by
  classical
  obtain ⟨P₀, K, K₀, H, A, G, W, hP₀, hP₀P, hP₀Ω,
      hK, hKs, hKcard, hK₀K, hK₀s, _, hHK, hsign,
      hA, hAs, hAc, hG, hGs, hGc, hW, hZW, hfixed, hgerm, hAv, hAe, hpos⟩ :=
    exists_face_graph_position_with_height_within (by simp) J P T hJ hP hT hcv hPJ
      hcard hvertices hedges ht ht3.le hZ hfront hΩ hZΩ height hlocal hε
  have hAK : A.space = H.map 1 '' K.space := by rw [hKs]; exact hAs
  have hKdisks : ∀ w ∈ K.space, w ∈ interior J.space →
      ∃ d rim : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d rim ∧ d ⊆ K.space ∧
        w ∈ d \ rim ∧ IsOpen ((Subtype.val : K.space → V3) ⁻¹' (d \ rim)) := by
    intro w hw hwJ
    obtain ⟨d, rim, hd, hdP, hwd, hopen⟩ := hdisks w (hKs.subset hw) hwJ
    refine ⟨d, rim, hd, hdP.trans hKs.symm.subset, hwd, ?_⟩
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hopen
    apply isOpen_induced_iff.mpr
    refine ⟨U, hU, ?_⟩
    ext x
    exact Set.ext_iff.mp hUeq ⟨x, hKs.subset x.property⟩
  have hAdisks : ∀ w ∈ A.space, w ∈ interior J.space →
      ∃ d rim : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d rim ∧ d ⊆ A.space ∧
        w ∈ d \ rim ∧ IsOpen ((Subtype.val : A.space → V3) ⁻¹' (d \ rim)) := by
    intro w hw hwJ
    have hbackK : (H.map 1).symm w ∈ K.space := by
      obtain ⟨x, hx, rfl⟩ := hAK.subset hw
      simpa only [Homeomorph.symm_apply_apply] using hx
    have hbackJ : (H.map 1).symm w ∈ interior J.space := by
      by_contra hn
      have hfix := H.outside 1 ((H.map 1).symm w) hn
      rw [(H.map 1).apply_symm_apply] at hfix
      exact hn (hfix ▸ hwJ)
    obtain ⟨d, rim, hd, hdK, hpd, hopen⟩ := hKdisks _ hbackK hbackJ
    obtain ⟨d', rim', hd', hd'A, hwd', hopen'⟩ :=
      K.exists_moved_disk_neighborhood A hK (H.map 1) hHK hAK hd hdK hpd hopen
    exact ⟨d', rim', hd', hd'A, by simpa only [Homeomorph.apply_symm_apply] using hwd', hopen'⟩
  refine ⟨P₀, H, A, G, W, hP₀, hP₀P, hA, hAs, hAc, hG, hGs, hGc,
    hW, hZW, hfixed, hgerm, hAv, hAe, hpos, ?_, ?_⟩
  · intro w hwG hwt
    have hwJ : w ∈ interior J.space := htJ (intrinsicInterior_subset hwt)
    by_cases hw₀ : w ∈ P₀.space
    · have hwP : w ∈ P.space := hP₀P hw₀
      have hwΩ : w ∈ Ω := hP₀Ω ⟨hw₀, intrinsicInterior_subset hwt⟩
      obtain ⟨⟨u, v, hu, hv, hinter, hsection⟩, hneg, hpositive⟩ :=
        hregular w ⟨⟨hwP, hwt⟩, hwΩ⟩
      obtain ⟨d, rim, hd, hdK, hwd, hopen⟩ := hKdisks w (hKs.symm.subset hwP) hwJ
      have htarget : ∀ᶠ x in 𝓝 w, x ∈ convexHull ℝ (t : Set V3) ↔ height x = 0 := by
        filter_upwards [Set.eventually_mem_iff_mem_affineSpan_of_intrinsicInterior hwt] with x hx
        rw [affineSpan_convexHull] at hx
        exact hx.trans (hheight x).symm
      have hGlocal : ∀ᶠ x in 𝓝 w,
          x ∈ G.space ↔ x ∈ H.map 1 '' K.space ∩ {x | height x = 0} := by
        filter_upwards [htarget] with x hx
        rw [hGs, hAK, mem_inter_iff, hx]
        rfl
      apply K.ncard_graph_degree_after_face_affine_motion_on_protected_subcomplex K₀ G
        hK hKcard hK₀K hG hGc (hK₀s.symm.subset hw₀) hwG hd hdK hwd hopen
        height hu hv hinter (by simpa only [hKs] using hsection)
        (by simpa only [hKs] using hneg) (by simpa only [hKs] using hpositive)
        (H.map 1) hHK (fun x hx => H.fixed_protected 1 x (hK₀s.subset hx))
        (fun x hx => (hsign 1 x hx).2) (fun x hx => (hsign 1 x hx).1) hGlocal
    · exact A.ncard_face_graph_neighbors_of_local_disks_outside_protection J T G hA hAc
        hAdisks ht ht3 hG hGs hGc hpos hwG hwJ hw₀ hwt
  · rintro w ⟨hwA, hwt⟩
    have hwzero : height w = 0 :=
      (hheight w).mpr (convexHull_subset_affineSpan _ (intrinsicInterior_subset hwt))
    by_cases hw₀ : w ∈ P₀.space
    · have hwP : w ∈ P.space := hP₀P hw₀
      have hwΩ : w ∈ Ω := hP₀Ω ⟨hw₀, intrinsicInterior_subset hwt⟩
      have hsigns := (hregular w ⟨⟨hwP, hwt⟩, hwΩ⟩).2
      have hfw : H.map 1 w = w := H.fixed_protected 1 w hw₀
      have hnew := hHK.mem_both_height_closures_image hK height height
        (fun x hx => (hsign 1 x hx).2) (fun x hx => (hsign 1 x hx).1)
        (by simpa only [hKs] using hsigns) (by rw [hfw]; exact hwzero)
      simpa only [hfw, ← hAK] using hnew
    · obtain ⟨a, ha, hwa⟩ := A.exists_face_intrinsicInterior_of_finite hA hwA
      have hspan : affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ := by
        rcases hpos a ha with hprotected | hspan | hdisjoint
        · exact False.elim (hw₀ (hprotected (intrinsicInterior_subset hwa)))
        · exact hspan
        · exact False.elim (disjoint_left.mp hdisjoint hwa (intrinsicInterior_subset hwt))
      let V := affineSpan ℝ (t : Set V3)
      have hVdim : finrank ℝ V.direction = 2 := T.finrank_faceDirection_of_card ht ht3
      have hVtop : V ≠ ⊤ := by
        intro heq
        rw [heq, AffineSubspace.direction_top, finrank_top] at hVdim
        norm_num at hVdim
      have hne : ∃ v ∈ a, height v ≠ 0 :=
        V.exists_nonzero_height_vertex_of_span_union_eq_top hVtop height hheight
          (subset_affineSpan ℝ _) hspan
      have hsigns := Set.mem_both_height_closures_of_intrinsicInterior_convexHull
        a height hwa hwzero hne
      exact ⟨closure_mono (inter_subset_inter_left _ (A.convexHull_subset_space ha)) hsigns.1,
        closure_mono (inter_subset_inter_left _ (A.convexHull_subset_space ha)) hsigns.2⟩



theorem exists_regular_protected_face_graph_position
    (J P T : SimplicialComplex ℝ V3)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hPJ : P.space ⊆ J.space)
    (hcard : ∀ s ∈ P.faces, s.card ≤ 3)
    (hvertices : Disjoint P.space T.vertices)
    (hedges : ∀ a ∈ T.faces, a.card = 2 →
      (P.space ∩ convexHull ℝ (a : Set V3)).Finite)
    {t : Finset V3} (ht : t ∈ T.faces) (ht3 : t.card = 3)
    (htJ : convexHull ℝ (t : Set V3) ⊆ interior J.space)
    {Z : Set V3} (hZ : IsClosed Z) (hfront : frontier J.space ⊆ Z)
    {Ω : Set V3} (hΩ : IsOpen Ω)
    (hZΩ : P.space ∩ Z ∩ convexHull ℝ (t : Set V3) ⊆ Ω)
    (height : V3 →ᵃ[ℝ] ℝ)
    (hheight : ∀ x, height x = 0 ↔ x ∈ affineSpan ℝ (t : Set V3))
    (hlocal : ∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set V3),
      ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ V3),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set V3) ∩ U, ∃ L ∈ Q, y ∈ L)
    (hdisks : ∀ w ∈ P.space, w ∈ interior J.space →
      ∃ d rim : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d rim ∧ d ⊆ P.space ∧
        w ∈ d \ rim ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ rim)))
    (hregular : ∀ w ∈ (P.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) ∩ Ω,
      (∃ u v : V3, u ≠ w ∧ v ≠ w ∧ segment ℝ w u ∩ segment ℝ w v ⊆ {w} ∧
        ∀ᶠ x in 𝓝 w, x ∈ P.space ∩ {x | height x = 0} ↔
          x ∈ segment ℝ w u ∪ segment ℝ w v) ∧
      w ∈ closure (P.space ∩ {x | height x < 0}) ∧
      w ∈ closure (P.space ∩ {x | 0 < height x}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P₀ : SimplicialComplex ℝ V3) (H : PLCarrierMotion J.space P₀.space ε)
      (A G : SimplicialComplex ℝ V3) (W : Set V3),
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧
      (∀ a ∈ A.faces, a.card ≤ 3) ∧
      G.faces.Finite ∧ G.space = A.space ∩ convexHull ℝ (t : Set V3) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      IsOpen W ∧ Z ⊆ W ∧
      (∀ τ, EqOn (H.map τ) id W) ∧
      (∀ τ, H.map τ '' P.space ∩ W = P.space ∩ W) ∧
      Disjoint A.space T.vertices ∧
      (∀ a ∈ T.faces, a.card ≤ 2 →
        (A.space ∩ convexHull ℝ (a : Set V3)).Finite) ∧
      (∀ a ∈ A.faces,
        convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
              (convexHull ℝ (t : Set V3))) ∧
      ∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)) →
          (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2 := by
  obtain ⟨P₀, H, A, G, W, hP₀, hP₀P, hA, hAs, hAc, hG, hGs, hGc,
      hW, hZW, hfixed, hgerm, hAv, hAe, hpos, hdegree, _⟩ :=
    exists_signed_regular_protected_face_graph_position J P T hJ hP hT hcv hPJ hcard
      hvertices hedges ht ht3 htJ hZ hfront hΩ hZΩ height hheight hlocal hdisks hregular hε
  exact ⟨P₀, H, A, G, W, hP₀, hP₀P, hA, hAs, hAc, hG, hGs, hGc,
    hW, hZW, hfixed, hgerm, hAv, hAe, hpos, hdegree⟩

end Geometry.SimplicialComplex
