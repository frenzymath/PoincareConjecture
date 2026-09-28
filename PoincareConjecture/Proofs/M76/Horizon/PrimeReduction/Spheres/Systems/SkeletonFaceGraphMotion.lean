import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.TriangleRegularCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OtherFaceProtection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.OriginalWholeFaceGraphDegreeMotion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.FaceGraphCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MovedLocalDisks













set_option autoImplicit false

open Set Geometry Module

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_original_sphere_system_other_faces_graph_motion_with_crossings
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgc : ContinuousOn g K.space)
    (hgi : InjOn g K.space) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {D : Set X} (hD : IsClosed D) (hSD : Disjoint (⋃ i, S i) D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (J P P₀ : SimplicialComplex ℝ V3)
      (H : PLCarrierMotion J.space P₀.space ε)
      (M G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W : Set X),
      J.faces.Finite ∧ Convex ℝ J.space ∧
      convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space ∧ J.space ⊆ Q.target ∧
      P.faces.Finite ∧ P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space ∧
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      M.faces.Finite ∧ M.space = H.map 1 '' P.space ∧ M.space ⊆ J.space ∧
      (∀ a ∈ M.faces, a.card ≤ 3) ∧
      (∀ a ∈ M.faces,
        convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set V3) ∪ A '' (s : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
              (convexHull ℝ (A '' (s : Set E)))) ∧
      G.faces.Finite ∧ G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ x ∈ Q.target, Phi (Q.symm x) = Q.symm (H.map 1 x)) ∧
      EqOn Phi id (Q.symm '' J.space)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space) ∧
      IsOpen W ∧ D ⊆ W ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      EqOn Phi id W ∧ Phi '' (⋃ i, S i) ∩ W = (⋃ i, S i) ∩ W ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (Phi '' S i) K g a) ∧
      (Pairwise fun i j => Disjoint (Phi '' S i) (Phi '' S j)) ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      ∀ w ∈ M.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0 := by
  classical
  obtain ⟨t, T, J, P, Z, Ω, L, htimage, ht3, hT, ht, hTs, hJ, hcv, hTJ, hJQ,
      hP, hPs, hPc, hPv, hPe, hZeq, hZ, hfront, hcover, _, hLplane,
      hΩ, _, hZΩ, hregular⟩ :=
    exists_original_sphere_system_triangle_regular_cover S sS hdisjoint K g hgi hSV hs hs3
      (fun a ha _ ha2 => hedges a ha ha2) (fun i a ha _ ha2 => hcofaces i a ha ha2)
      Q hQ A hmap hA
  have hPJ : P.space ⊆ J.space := by rw [hPs]; exact inter_subset_right
  have hlocal : ∀ x ∈ J.space, Q.symm x ∈ ⋃ i, S i ↔ x ∈ P.space := by
    intro x hxJ
    rw [hPs]
    constructor
    · intro hx
      exact ⟨⟨Q.symm x, ⟨hx, Q.map_target (hJQ hxJ)⟩,
        Q.right_inv (hJQ hxJ)⟩, hxJ⟩
    · rintro ⟨⟨y, hy, rfl⟩, _⟩
      simpa only [Q.left_inv hy.2] using hy.1
  have hboundary : intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) ⊆ Z := by
    intro x hx
    have hxt : x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) := by
      simpa only [htimage, Finset.coe_image] using hx
    obtain ⟨v, hv, hxv⟩ := (T.indep ht).mem_intrinsicFrontier_convexHull_finset
      (T.nonempty_of_mem_faces ht) x |>.mp hxt
    have hcard : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv, ht3]
    have hface : t.erase v ∈ T.faces := T.down_closed ht (Finset.erase_subset _ _)
      (Finset.card_pos.mp (by omega))
    rw [hZeq]
    exact Or.inl (mem_iUnion₂.mpr ⟨t.erase v, hface, mem_iUnion.mpr ⟨hcard, hxv⟩⟩)
  obtain ⟨C, hC, hZC, hfrontC, hskC, hCface⟩ :=
    exists_original_other_faces_coordinate_protection K hK g hgc hgi hs hs3
      Q A hmap hA J hJ hJQ hZ hfront hboundary
  have hCtoZ {x : V3} (hxC : x ∈ C) (hxt : x ∈ convexHull ℝ (t : Set V3)) : x ∈ Z := by
    have hxt' : x ∈ convexHull ℝ (A '' (s : Set E)) := by
      simpa only [htimage, Finset.coe_image] using hxt
    exact (hCface.subset ⟨hxC, hxt'⟩).1
  have hcoverC : ∀ x ∈ P.space ∩ C ∩ convexHull ℝ (t : Set V3),
      ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧
        ∃ B : Finset (AffineSubspace ℝ V3),
          (∀ L ∈ B, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set V3) ∩ U, ∃ L ∈ B, y ∈ L :=
    fun x hx => hcover x ⟨⟨hx.1.1, hCtoZ hx.1.2 hx.2⟩, hx.2⟩
  have hCΩ : P.space ∩ C ∩ convexHull ℝ (t : Set V3) ⊆ Ω :=
    fun x hx => hZΩ ⟨⟨hx.1.1, hCtoZ hx.1.2 hx.2⟩, hx.2⟩
  obtain ⟨P₀, H, M, G, Phi, W₀, W₁, hP₀, hP₀P, hM, hMs, hMJ, hMc,
      hG, hGs, hGc, hW₀, hZW₀, hHfixed, _, _, _, hpos, hPhiQ, hPhiout, _,
      hPhiPL, hPhiinv, hPhiS, hW₁, hDW₁, hPhiW₁, _, hdegree, hsigns⟩ :=
    exists_original_whole_face_graph_motion_with_signed_degree e he Q hQ J P T hJ hP hT
      hcv hPJ hJQ hPc hPv hPe ht ht3 (by rw [← hTs]; exact hTJ)
      (⋃ i, S i) hlocal hD hSD hC hfrontC hcoverC hΩ hCΩ L hLplane
      (fun w hw hwJ => exists_finite_sphere_system_clipped_disk_neighborhood S sS hdisjoint Q hQ J P hJ hJQ hPs hw hwJ)
      hregular hε
  have hthull : convexHull ℝ (t : Set V3) = convexHull ℝ (A '' (s : Set E)) := by
    rw [htimage, Finset.coe_image]
  have htriangle : convexHull ℝ (A '' (s : Set E)) =
      (Q ∘ g) '' convexHull ℝ (s : Set E) :=
    (A.toAffineMap.image_convexHull _).symm.trans (image_congr hA).symm
  have htriangleJ : convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space := by
    rw [← hthull, ← hTs]
    exact hTJ
  have hGs' : G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) := by
    rw [hGs, hthull]
  have hpos' : ∀ a ∈ M.faces,
      convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
        affineSpan ℝ ((a : Set V3) ∪ A '' (s : Set E)) = ⊤ ∨
          Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
            (convexHull ℝ (A '' (s : Set E))) := by
    simpa only [htimage, Finset.coe_image] using hpos
  have hphysical : Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxM, hxt⟩ := hGs'.subset hx
      obtain ⟨z, hz, hzx⟩ := htriangle.subset hxt
      have hsymm : Q.symm x = g z := by
        rw [← hzx]
        exact Q.left_inv (hmap hz)
      exact ⟨(hPhiS x (hMJ hxM)).mpr hxM, ⟨z, hz, hsymm.symm⟩⟩
    · rintro ⟨hyS, z, hz, rfl⟩
      have hzt : Q (g z) ∈ convexHull ℝ (A '' (s : Set E)) :=
        htriangle.symm.subset ⟨z, hz, rfl⟩
      have hzJ := interior_subset (htriangleJ hzt)
      refine ⟨Q (g z), hGs'.symm.subset ⟨?_, hzt⟩, Q.left_inv (hmap hz)⟩
      exact (hPhiS _ hzJ).mp (by simpa only [Q.left_inv (hmap hz)] using hyS)
  let W := (W₁ ∪ (Q.source ∩ Q ⁻¹' W₀)) ∪ (Q.symm '' J.space)ᶜ
  have hQJclosed : IsClosed (Q.symm '' J.space) :=
    ((J.isCompact_space_of_finite hJ).image_of_continuousOn
      (Q.symm.continuousOn.mono hJQ)).isClosed
  have hW : IsOpen W := (hW₁.union (Q.isOpen_inter_preimage hW₀)).union hQJclosed.isOpen_compl
  have hPhiW : EqOn Phi id W := by
    intro y hy
    rcases hy with (hy | ⟨hyQ, hyW₀⟩) | hyout
    · exact hPhiW₁ hy
    · have h := hPhiQ (Q y) (Q.map_source hyQ)
      simpa only [Q.left_inv hyQ, hHfixed 1 hyW₀, id_eq] using h
    · exact hPhiout hyout
  have hfacesW : ∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
      g '' convexHull ℝ (a : Set E) ⊆ W := by
    intro a ha ha3 hne y hy
    by_cases hyJ : y ∈ Q.symm '' J.space
    · obtain ⟨x, hxJ, rfl⟩ := hyJ
      refine Or.inl (Or.inr ⟨Q.map_target (hJQ hxJ), ?_⟩)
      change Q (Q.symm x) ∈ W₀
      rw [Q.right_inv (hJQ hxJ)]
      exact hZW₀ (hskC ⟨hxJ, mem_iUnion₂.mpr ⟨a, ha, mem_iUnion.mpr ⟨ha3, mem_iUnion.mpr ⟨hne, hy⟩⟩⟩⟩)
    · exact Or.inr hyJ
  have heW : ∀ a ∈ K.faces, a.card ≤ 2 →
      g '' convexHull ℝ (a : Set E) ⊆ W := by
    intro a ha ha2
    exact hfacesW a ha (by omega) (fun heq => by subst a; omega)
  refine ⟨J, P, P₀, H, M, G, Phi, W, hJ, hcv, htriangleJ, hJQ, hP, hPs,
    hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos', hG, hGs', hGc, hphysical, hPhiQ,
    hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW₁.trans (subset_union_left.trans subset_union_left),
    hfacesW, hPhiW, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hxW⟩
      have hyx' : y = x := Phi.injective (hyx.trans (hPhiW hxW).symm)
      exact ⟨hyx' ▸ hy, hxW⟩
    · rintro ⟨hx, hxW⟩
      exact ⟨⟨x, hx, hPhiW hxW⟩, hxW⟩
  · intro i a ha ha2
    apply (hcofaces i a ha ha2).image_of_disjoint_support Phi hW.isClosed_compl
    · exact disjoint_left.mpr (fun x hx hxedge => hx (heW a ha ha2.le hxedge))
    · simpa only [compl_compl] using hPhiW

  · intro i j hij
    exact (hdisjoint hij).image Phi.injective.injOn (subset_univ _) (subset_univ _)
  · simpa only [hthull] using hdegree
  · rintro w ⟨hwM, hwt⟩ O hO hwO
    have hwt' : w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)) := by
      simpa only [hthull] using hwt
    obtain ⟨d, rim, hd, hdM, hwd, hopen⟩ :=
      exists_moved_finite_sphere_system_clipped_disk_neighborhood S sS hdisjoint
        Q hQ J P M hJ hJQ hPs H hMs hwM
        (htriangleJ (intrinsicInterior_subset hwt))
    have h := J.exists_face_graph_crossing_chart M G hJ hM hMJ hMc hG hGc hGs
      (by rw [hthull]; exact htriangleJ) L hLplane hwM hwt'
      (fun hwG => hdegree w hwG hwt') hd hdM hwd hopen
      (hsigns w ⟨hwM, hwt'⟩).1 (hsigns w ⟨hwM, hwt'⟩).2 hO hwO
    simpa only [hthull] using h


theorem exists_original_sphere_system_skeleton_face_graph_motion_with_crossings
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgc : ContinuousOn g K.space)
    (hgi : InjOn g K.space) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {D : Set X} (hD : IsClosed D) (hSD : Disjoint (⋃ i, S i) D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (J P P₀ : SimplicialComplex ℝ V3)
      (H : PLCarrierMotion J.space P₀.space ε)
      (M G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W : Set X),
      J.faces.Finite ∧ Convex ℝ J.space ∧
      convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space ∧ J.space ⊆ Q.target ∧
      P.faces.Finite ∧ P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space ∧
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      M.faces.Finite ∧ M.space = H.map 1 '' P.space ∧ M.space ⊆ J.space ∧
      (∀ a ∈ M.faces, a.card ≤ 3) ∧
      (∀ a ∈ M.faces,
        convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set V3) ∪ A '' (s : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
              (convexHull ℝ (A '' (s : Set E)))) ∧
      G.faces.Finite ∧ G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      Q.symm '' G.space = Phi '' (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ x ∈ Q.target, Phi (Q.symm x) = Q.symm (H.map 1 x)) ∧
      EqOn Phi id (Q.symm '' J.space)ᶜ ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space) ∧
      IsOpen W ∧ D ⊆ W ∧
      (∀ a ∈ K.faces, a.card ≤ 2 →
        g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      EqOn Phi id W ∧ Phi '' (⋃ i, S i) ∩ W = (⋃ i, S i) ∩ W ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (Phi '' S i) K g a) ∧
      (Pairwise fun i j => Disjoint (Phi '' S i) (Phi '' S j)) ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      ∀ w ∈ M.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 ((ℝ × ℝ) × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0 := by
  obtain ⟨J, P, P₀, H, M, G, Phi, W, hJ, hcv, htriangleJ, hJQ, hP, hPs,
      hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc, hphysical, hPhiQ,
      hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW, hfacesW, hrest⟩ :=
    exists_original_sphere_system_other_faces_graph_motion_with_crossings
      S sS hdisjoint he K hK g hgc hgi hSV hs hs3 hedges hcofaces Q hQ A hmap hA hD hSD hε
  refine ⟨J, P, P₀, H, M, G, Phi, W, hJ, hcv, htriangleJ, hJQ, hP, hPs,
    hP₀, hP₀P, hM, hMs, hMJ, hMc, hpos, hG, hGs, hGc, hphysical, hPhiQ,
    hPhiout, hPhiPL, hPhiinv, hPhiS, hW, hDW, ?_, hrest⟩
  intro a ha ha2
  exact hfacesW a ha (by omega) (fun heq => by subst a; omega)

end PoincareConjecture.M76
