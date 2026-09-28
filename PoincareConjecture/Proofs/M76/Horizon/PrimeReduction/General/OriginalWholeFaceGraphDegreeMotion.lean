import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.RegularProtectedFaceGraphPosition
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartSurfaceMotion











set_option autoImplicit false

open Set Geometry Module

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Filter
open scoped Topology





theorem exists_original_whole_face_graph_motion_with_signed_degree
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (J P T : SimplicialComplex ℝ V3)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hPJ : P.space ⊆ J.space)
    (hJB : J.space ⊆ B.target)
    (hcard : ∀ a ∈ P.faces, a.card ≤ 3)
    (hvertices : Disjoint P.space T.vertices)
    (hedges : ∀ a ∈ T.faces, a.card = 2 →
      (P.space ∩ convexHull ℝ (a : Set V3)).Finite)
    {t : Finset V3} (ht : t ∈ T.faces) (ht3 : t.card = 3)
    (htJ : convexHull ℝ (t : Set V3) ⊆ interior J.space)
    (S : Set X) (hlocal : ∀ x ∈ J.space, B.symm x ∈ S ↔ x ∈ P.space)
    {D : Set X} (hD : IsClosed D) (hSD : Disjoint S D)
    {C : Set V3} (hC : IsClosed C) (hfront : frontier J.space ⊆ C)
    (hcover : ∀ x ∈ P.space ∩ C ∩ convexHull ℝ (t : Set V3),
      ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ V3),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set V3) ∩ U, ∃ L ∈ Q, y ∈ L)
    {Ω : Set V3} (hΩ : IsOpen Ω)
    (hCΩ : P.space ∩ C ∩ convexHull ℝ (t : Set V3) ⊆ Ω)
    (height : V3 →ᵃ[ℝ] ℝ)
    (hheight : ∀ x, height x = 0 ↔ x ∈ affineSpan ℝ (t : Set V3))
    (hdisks : ∀ w ∈ P.space, w ∈ interior J.space →
      ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
        w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)))
    (hregular : ∀ w ∈ (P.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) ∩ Ω,
      (∃ u v : V3, u ≠ w ∧ v ≠ w ∧ segment ℝ w u ∩ segment ℝ w v ⊆ {w} ∧
        ∀ᶠ x in 𝓝 w, x ∈ P.space ∩ {y | height y = 0} ↔
          x ∈ segment ℝ w u ∪ segment ℝ w v) ∧
      w ∈ closure (P.space ∩ {x | height x < 0}) ∧
      w ∈ closure (P.space ∩ {x | 0 < height x}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P₀ : SimplicialComplex ℝ V3) (H : PLCarrierMotion J.space P₀.space ε)
      (A G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W₀ : Set V3) (W : Set X),
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧ A.space ⊆ J.space ∧
      (∀ a ∈ A.faces, a.card ≤ 3) ∧
      G.faces.Finite ∧ G.space = A.space ∩ convexHull ℝ (t : Set V3) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      IsOpen W₀ ∧ C ⊆ W₀ ∧
      (∀ τ, EqOn (H.map τ) id W₀) ∧
      (∀ τ, H.map τ '' P.space ∩ W₀ = P.space ∩ W₀) ∧
      Disjoint A.space T.vertices ∧
      (∀ a ∈ T.faces, a.card ≤ 2 →
        (A.space ∩ convexHull ℝ (a : Set V3)).Finite) ∧
      (∀ a ∈ A.faces,
        convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
              (convexHull ℝ (t : Set V3))) ∧
      (∀ x ∈ B.target, Phi (B.symm x) = B.symm (H.map 1 x)) ∧
      EqOn Phi id (B.symm '' J.space)ᶜ ∧ EqOn Phi id (B.symm '' P₀.space) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, B.symm x ∈ Phi '' S ↔ x ∈ A.space) ∧
      IsOpen W ∧ D ⊆ W ∧ EqOn Phi id W ∧ Phi '' S ∩ W = S ∩ W ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) ∧
      ∀ w ∈ A.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)),
        w ∈ closure (A.space ∩ {x | height x < 0}) ∧
          w ∈ closure (A.space ∩ {x | 0 < height x}) := by
  have hJc := J.isCompact_space_of_finite hJ
  let Z := C ∪ (J.space ∩ B.symm ⁻¹' D)
  have hZ : IsClosed Z := hC.union
    ((B.symm.continuousOn.mono hJB).preimage_isClosed_of_isClosed hJc.isClosed hD)
  have hZcover : ∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set V3),
      ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ V3),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set V3) ∩ U, ∃ L ∈ Q, y ∈ L := by
    rintro x ⟨⟨hxP, hxZ⟩, hxt⟩
    rcases hxZ with hxC | hxD
    · exact hcover x ⟨⟨hxP, hxC⟩, hxt⟩
    · exact (disjoint_left.mp hSD ((hlocal x hxD.1).mpr hxP) hxD.2).elim
  have hZΩ : P.space ∩ Z ∩ convexHull ℝ (t : Set V3) ⊆ Ω := by
    rintro x ⟨⟨hxP, hxZ⟩, hxt⟩
    rcases hxZ with hxC | hxD
    · exact hCΩ ⟨⟨hxP, hxC⟩, hxt⟩
    · exact (disjoint_left.mp hSD ((hlocal x hxD.1).mpr hxP) hxD.2).elim
  obtain ⟨P₀, H, A, G, W₀, hP₀, hP₀P, hA, hAs, hAc,
      hG, hGs, hGc, hW₀, hZW₀, hfixed, hgerm, hAv, hAe, hpos, hdegree, hsigns⟩ :=
    SimplicialComplex.exists_signed_regular_protected_face_graph_position
      J P T hJ hP hT hcv hPJ hcard hvertices hedges ht ht3 htJ hZ
      (hfront.trans subset_union_left) hΩ hZΩ height hheight hZcover hdisks hregular hε
  obtain ⟨Phi, hPhiB, hPhiout, hPhiprot, hPhiPL, hPhiinv, hPhiS⟩ :=
    exists_original_chart_surface_motion e he B hB J hJ hJB
      (hP₀P.trans hPJ) H S P.space hlocal
  have hAJ : A.space ⊆ J.space := by
    rintro x hx
    obtain ⟨p, hp, rfl⟩ := hAs.subset hx
    exact (H.carrier 1).subset ⟨p, hPJ hp, rfl⟩
  let W := (B.source ∩ B ⁻¹' W₀) ∪ (B.symm '' J.space)ᶜ
  have hW : IsOpen W := (B.isOpen_inter_preimage hW₀).union
    (hJc.image_of_continuousOn (B.symm.continuousOn.mono hJB)).isClosed.isOpen_compl
  have hDW : D ⊆ W := by
    intro y hyD
    by_cases hyJ : y ∈ B.symm '' J.space
    · obtain ⟨x, hxJ, rfl⟩ := hyJ
      exact Or.inl ⟨B.map_target (hJB hxJ), by
        change B (B.symm x) ∈ W₀
        rw [B.right_inv (hJB hxJ)]
        exact hZW₀ (Or.inr ⟨hxJ, hyD⟩)⟩
    · exact Or.inr hyJ
  have hPhiW : EqOn Phi id W := by
    intro y hy
    rcases hy with ⟨hyB, hyW₀⟩ | hyout
    · have h := hPhiB (B y) (B.map_source hyB)
      simpa only [B.left_inv hyB, hfixed 1 hyW₀, id_eq] using h
    · exact hPhiout hyout
  refine ⟨P₀, H, A, G, Phi, W₀, W, hP₀, hP₀P, hA, hAs, hAJ, hAc,
    hG, hGs, hGc, hW₀, subset_union_left.trans hZW₀, hfixed, hgerm,
    hAv, hAe, hpos, hPhiB, hPhiout, hPhiprot, hPhiPL, hPhiinv, ?_,
    hW, hDW, hPhiW, ?_, hdegree, hsigns⟩
  · intro x hx
    simpa only [hAs] using hPhiS x hx
  · ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hxW⟩
      have hyx' : y = x := Phi.injective (hyx.trans (hPhiW hxW).symm)
      exact ⟨hyx' ▸ hy, hxW⟩
    · rintro ⟨hx, hxW⟩
      exact ⟨⟨x, hx, hPhiW hxW⟩, hxW⟩


theorem exists_original_whole_face_graph_motion_with_degree
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (J P T : SimplicialComplex ℝ V3)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hPJ : P.space ⊆ J.space)
    (hJB : J.space ⊆ B.target)
    (hcard : ∀ a ∈ P.faces, a.card ≤ 3)
    (hvertices : Disjoint P.space T.vertices)
    (hedges : ∀ a ∈ T.faces, a.card = 2 →
      (P.space ∩ convexHull ℝ (a : Set V3)).Finite)
    {t : Finset V3} (ht : t ∈ T.faces) (ht3 : t.card = 3)
    (htJ : convexHull ℝ (t : Set V3) ⊆ interior J.space)
    (S : Set X) (hlocal : ∀ x ∈ J.space, B.symm x ∈ S ↔ x ∈ P.space)
    {D : Set X} (hD : IsClosed D) (hSD : Disjoint S D)
    {C : Set V3} (hC : IsClosed C) (hfront : frontier J.space ⊆ C)
    (hcover : ∀ x ∈ P.space ∩ C ∩ convexHull ℝ (t : Set V3),
      ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ V3),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set V3) ∩ U, ∃ L ∈ Q, y ∈ L)
    {Ω : Set V3} (hΩ : IsOpen Ω)
    (hCΩ : P.space ∩ C ∩ convexHull ℝ (t : Set V3) ⊆ Ω)
    (height : V3 →ᵃ[ℝ] ℝ)
    (hheight : ∀ x, height x = 0 ↔ x ∈ affineSpan ℝ (t : Set V3))
    (hdisks : ∀ w ∈ P.space, w ∈ interior J.space →
      ∃ d q : Set V3, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ P.space ∧
        w ∈ d \ q ∧ IsOpen ((Subtype.val : P.space → V3) ⁻¹' (d \ q)))
    (hregular : ∀ w ∈ (P.space ∩ intrinsicInterior ℝ (convexHull ℝ (t : Set V3))) ∩ Ω,
      (∃ u v : V3, u ≠ w ∧ v ≠ w ∧ segment ℝ w u ∩ segment ℝ w v ⊆ {w} ∧
        ∀ᶠ x in 𝓝 w, x ∈ P.space ∩ {y | height y = 0} ↔
          x ∈ segment ℝ w u ∪ segment ℝ w v) ∧
      w ∈ closure (P.space ∩ {x | height x < 0}) ∧
      w ∈ closure (P.space ∩ {x | 0 < height x}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P₀ : SimplicialComplex ℝ V3) (H : PLCarrierMotion J.space P₀.space ε)
      (A G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W₀ : Set V3) (W : Set X),
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧ A.space ⊆ J.space ∧
      (∀ a ∈ A.faces, a.card ≤ 3) ∧
      G.faces.Finite ∧ G.space = A.space ∩ convexHull ℝ (t : Set V3) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      IsOpen W₀ ∧ C ⊆ W₀ ∧
      (∀ τ, EqOn (H.map τ) id W₀) ∧
      (∀ τ, H.map τ '' P.space ∩ W₀ = P.space ∩ W₀) ∧
      Disjoint A.space T.vertices ∧
      (∀ a ∈ T.faces, a.card ≤ 2 →
        (A.space ∩ convexHull ℝ (a : Set V3)).Finite) ∧
      (∀ a ∈ A.faces,
        convexHull ℝ (a : Set V3) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set V3) ∪ (t : Set V3)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
              (convexHull ℝ (t : Set V3))) ∧
      (∀ x ∈ B.target, Phi (B.symm x) = B.symm (H.map 1 x)) ∧
      EqOn Phi id (B.symm '' J.space)ᶜ ∧ EqOn Phi id (B.symm '' P₀.space) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, B.symm x ∈ Phi '' S ↔ x ∈ A.space) ∧
      IsOpen W ∧ D ⊆ W ∧ EqOn Phi id W ∧ Phi '' S ∩ W = S ∩ W ∧
      (∀ w (hwG : w ∈ G.vertices),
        w ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨w, hwG⟩).ncard = 2) := by
  obtain ⟨P₀, H, A, G, Phi, W₀, W, hP₀, hP₀P, hA, hAs, hAJ, hAc,
      hG, hGs, hGc, hW₀, hCW₀, hfixed, hgerm, hAv, hAe, hpos, hPhiB,
      hPhiout, hPhiprot, hPhiPL, hPhiinv, hPhiS, hW, hDW, hPhiW, hagree, hdegree, _⟩ :=
    exists_original_whole_face_graph_motion_with_signed_degree e he B hB J P T
      hJ hP hT hcv hPJ hJB hcard hvertices hedges ht ht3 htJ S hlocal hD hSD
      hC hfront hcover hΩ hCΩ height hheight hdisks hregular hε
  exact ⟨P₀, H, A, G, Phi, W₀, W, hP₀, hP₀P, hA, hAs, hAJ, hAc,
    hG, hGs, hGc, hW₀, hCW₀, hfixed, hgerm, hAv, hAe, hpos, hPhiB,
    hPhiout, hPhiprot, hPhiPL, hPhiinv, hPhiS, hW, hDW, hPhiW, hagree, hdegree⟩

end PoincareConjecture.M76
