import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.TransverseFaceGraph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.ClosedSetProtectedSurfacePosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.ProtectedFaceCarrier











set_option autoImplicit false

open Set Module unitInterval

namespace Geometry.SimplicialComplex



theorem exists_face_graph_position_with_height_within
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 3)
    (J P T : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hPJ : P.space ⊆ J.space)
    (hcard : ∀ s ∈ P.faces, s.card ≤ 3)
    (hvertices : Disjoint P.space T.vertices)
    (hedges : ∀ a ∈ T.faces, a.card = 2 →
      (P.space ∩ convexHull ℝ (a : Set E)).Finite)
    {t : Finset E} (ht : t ∈ T.faces) (htc : t.card ≤ 3)
    {Z : Set E} (hZ : IsClosed Z) (hfront : frontier J.space ⊆ Z)
    {Ω : Set E} (hΩ : IsOpen Ω)
    (hZΩ : P.space ∩ Z ∩ convexHull ℝ (t : Set E) ⊆ Ω)
    (height : E →ᵃ[ℝ] ℝ)
    (hlocal : ∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set E),
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ E),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set E) ∩ U, ∃ L ∈ Q, y ∈ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P₀ K K₀ : SimplicialComplex ℝ E) (H : PLCarrierMotion J.space P₀.space ε)
      (A G : SimplicialComplex ℝ E) (W : Set E),
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      P₀.space ∩ convexHull ℝ (t : Set E) ⊆ Ω ∧
      K.faces.Finite ∧ K.space = P.space ∧
      (∀ s ∈ K.faces, s.card ≤ 3) ∧
      K₀ ≤ K ∧ K₀.space = P₀.space ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      K.AffineOnFaces (H.map 1) ∧
      (∀ τ v, v ∈ K.vertices →
        (height v < 0 → height (H.map τ v) < 0) ∧
        (0 < height v → 0 < height (H.map τ v))) ∧
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧
      (∀ a ∈ A.faces, a.card ≤ 3) ∧
      G.faces.Finite ∧ G.space = A.space ∩ convexHull ℝ (t : Set E) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      IsOpen W ∧ Z ⊆ W ∧
      (∀ τ, EqOn (H.map τ) id W) ∧
      (∀ τ, H.map τ '' P.space ∩ W = P.space ∩ W) ∧
      Disjoint A.space T.vertices ∧
      (∀ a ∈ T.faces, a.card ≤ 2 →
        (A.space ∩ convexHull ℝ (a : Set E)).Finite) ∧
      (∀ a ∈ A.faces,
        convexHull ℝ (a : Set E) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set E) ∪ (t : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set E)))
              (convexHull ℝ (t : Set E))) := by
  obtain ⟨P₀, V, Q, hP₀, hP₀P, hV, hZV, hVP₀, hQ, hcover, hP₀Ω⟩ :=
    P.exists_protected_face_carrier_within hP t hZ hΩ hZΩ hlocal
  have hnear (x : P.space) (hx : (x : E) ∈ Z) :
      (Subtype.val ⁻¹' P₀.space : Set P.space) ∈ nhds x := by
    exact Filter.mem_of_superset (hV.mem_nhds (hZV hx))
      (fun y hy => hVP₀ ⟨y, hy, rfl⟩)
  have hboundary : P.space ∩ frontier J.space ⊆ P₀.space := by
    rintro x ⟨hx, hxJ⟩
    exact hVP₀ ⟨⟨x, hx⟩, hZV (hfront hxJ), rfl⟩
  have hP₀edges (a : Finset E) (ha : a ∈ T.faces) (hac : a.card = 2) :
      (P₀.space ∩ convexHull ℝ (a : Set E)).Finite :=
    (hedges a ha hac).subset (inter_subset_inter_left _ hP₀P)
  obtain ⟨K, K₀, H, A, hK, hKs, hKc, hK₀K, hK₀s, hfull, hHK, hsign,
      hA, hAs, hAc, hpos, hAv, hAe, _, _, W, hW, hZW, hfixed⟩ :=
    exists_closed_set_protected_surface_edge_position_with_height hdim J P P₀ T hJ hP hP₀ hT
      hcv hP₀P hPJ hboundary hZ hnear height hcard (hvertices.mono_left hP₀P) hP₀edges hε
  have hselected := fun a ha => (hpos a ha).imp_right (fun h => h t ht)
  obtain ⟨G, hG, hGs, hGc⟩ :=
    A.exists_face_intersection_graph_of_face_position hA hdim hAc
      (T.nonempty_of_mem_faces ht) htc Q hQ hcover hselected
  refine ⟨P₀, K, K₀, H, A, G, W, hP₀, hP₀P, hP₀Ω,
    hK, hKs, hKc, hK₀K, hK₀s, hfull, hHK, hsign, hA, hAs, hAc,
    hG, hGs, hGc, hW, hZW, hfixed, ?_, hAv, hAe, hselected⟩
  intro τ
  ext x
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hxW⟩
    have hyx' : y = x := (H.map τ).injective (hyx.trans (hfixed τ hxW).symm)
    exact ⟨hyx' ▸ hy, hxW⟩
  · rintro ⟨hx, hxW⟩
    exact ⟨⟨x, hx, hfixed τ hxW⟩, hxW⟩


theorem exists_face_graph_position_preserving_contact_germs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 3)
    (J P T : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hPJ : P.space ⊆ J.space)
    (hcard : ∀ s ∈ P.faces, s.card ≤ 3)
    (hvertices : Disjoint P.space T.vertices)
    (hedges : ∀ a ∈ T.faces, a.card = 2 →
      (P.space ∩ convexHull ℝ (a : Set E)).Finite)
    {t : Finset E} (ht : t ∈ T.faces) (htc : t.card ≤ 3)
    {Z : Set E} (hZ : IsClosed Z) (hfront : frontier J.space ⊆ Z)
    (hlocal : ∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set E),
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ E),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set E) ∩ U, ∃ L ∈ Q, y ∈ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P₀ : SimplicialComplex ℝ E) (H : PLCarrierMotion J.space P₀.space ε)
      (A G : SimplicialComplex ℝ E) (W : Set E),
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧
      (∀ a ∈ A.faces, a.card ≤ 3) ∧
      G.faces.Finite ∧ G.space = A.space ∩ convexHull ℝ (t : Set E) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      IsOpen W ∧ Z ⊆ W ∧
      (∀ τ, EqOn (H.map τ) id W) ∧
      (∀ τ, H.map τ '' P.space ∩ W = P.space ∩ W) ∧
      Disjoint A.space T.vertices ∧
      (∀ a ∈ T.faces, a.card ≤ 2 →
        (A.space ∩ convexHull ℝ (a : Set E)).Finite) ∧
      (∀ a ∈ A.faces,
        convexHull ℝ (a : Set E) ⊆ P₀.space ∨
          affineSpan ℝ ((a : Set E) ∪ (t : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set E)))
              (convexHull ℝ (t : Set E))) := by
  obtain ⟨P₀, K, K₀, H, A, G, W, hP₀, hP₀P, _, _, _, _, _, _, _, _, _, hrest⟩ :=
    exists_face_graph_position_with_height_within hdim J P T hJ hP hT hcv hPJ
      hcard hvertices hedges ht htc hZ hfront isOpen_univ (subset_univ _) 0 hlocal hε
  exact ⟨P₀, H, A, G, W, hP₀, hP₀P, hrest⟩

end Geometry.SimplicialComplex
