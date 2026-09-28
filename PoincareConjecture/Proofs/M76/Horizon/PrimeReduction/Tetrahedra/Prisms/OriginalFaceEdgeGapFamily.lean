import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleEdgeParameters

set_option autoImplicit false
open Set Geometry TriangularRoofModel
namespace PoincareConjecture.M76.PrismBelt
open TriangleCorner

theorem exists_original_face_edge_gap_family
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] [Finite ι]
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (d r : ι → Set E) (hd : ∀ i, IsFinitePLBallPair ℝ (d i) (r i))
    (hsub : ∀ i, d i ⊆ convexHull ℝ (s : Set E))
    (hrim : ∀ i, r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    (hdis : Pairwise fun i j => Disjoint (d i) (d j))
    (hvertex : ∀ i, Disjoint (d i) (s : Set E))
    (hnr : ∀ i, ∀ t : Finset E, t ⊆ s → t.card = 2 → ¬ r i ⊆ convexHull ℝ (t : Set E)) :
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (c : ι → Fin 3) (a b : ι → ℝ),
      Function.Injective F ∧ F '' vertices = (s : Set E) ∧
      F '' base = convexHull ℝ (s : Set E) ∧
      (∀ i, a i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i, b i ∈ Ioo (0 : ℝ) 1) ∧
      Nat.card {i : ι // ∃ j, c j = c i ∧ a i < a j} + Nat.card (range c) = Nat.card ι ∧
      Nat.card (range c) ≤ 3 ∧
      ∃ (n : {i : ι // ∃ j, c j = c i ∧ a i < a j} → ι)
        (M : {i : ι // ∃ j, c j = c i ∧ a i < a j} → Set E),
        Function.Injective M ∧
        ∀ i, c (n i) = c i ∧ a i < a (n i) ∧ b i < b (n i) ∧
          IsFinitePLBallPair (ℝ × ℝ) (M i)
            (d i ∪ (d (n i) ∪ F '' (cornerMap (c i) '' edgeIntervals (a i) (b i) (a (n i)) (b (n i))))) ∧
          M i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) =
            F '' (cornerMap (c i) '' edgeIntervals (a i) (b i) (a (n i)) (b (n i))) ∧
          M i ∩ (⋃ k, d k) = d i ∪ d (n i) ∧
          (∀ x ∈ M i \ (d i ∪ d (n i)),
            connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ k, d k) x = M i \ (d i ∪ d (n i)) ∧
            closure (connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ k, d k) x) = M i) ∧
          (∀ side : Bool,
            let e := originalRectangleEdge F (c i) side
            let lo := if side then a i else b i
            let hi := if side then a (n i) else b (n i)
            Function.Injective e ∧ ({e 0,e 1} : Finset E) ∈ K.faces ∧
              ({e 0,e 1} : Finset E) ⊆ s ∧ ({e 0,e 1} : Finset E).card = 2 ∧
              lo < hi ∧ Disjoint (e '' Ioo lo hi) (⋃ k, d k) ∧
              e lo ∈ ⋃ k, d k ∧ e hi ∈ ⋃ k, d k) ∧
          ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M i,
            G.IsFinitePL ∧
            (∀ x, (G x : E) ∈ d i ↔ (x : ℝ × ℝ).2 = 0) ∧
            (∀ x, (G x : E) ∈ d (n i) ↔ (x : ℝ × ℝ).2 = 1) ∧
            (∀ x, (G x : E) ∈ originalRectangleEdge F (c i) false '' Icc (b i) (b (n i)) ↔
              (x : ℝ × ℝ).1 = 0) ∧
            (∀ x, (G x : E) ∈ originalRectangleEdge F (c i) true '' Icc (a i) (a (n i)) ↔
              (x : ℝ × ℝ).1 = 1) := by
  obtain ⟨F,R,c,a,b,hRF,hFR,hface,hverts,hfront,ha,hb,hrcoords,hcard,hbound,n,M,hMinj,hdata⟩ :=
    exists_original_successor_rectangles_with_contacts K hs hs3 d r hd hsub hrim hdis hvertex hnr
  refine ⟨F,c,a,b,hRF.injective,hverts,hface,ha,hb,hcard,hbound,n,M,hMinj,?_⟩
  intro i
  obtain ⟨hnc,hlt,hM,hMQ,hother,hMT,hcomp,G,hG,hGW,hGZ,hGL,hGR⟩ := hdata i
  have hDQ := (hrim i).symm.trans (hrcoords i)
  have hZQ := (hrim (n i)).symm.trans (hrcoords (n i))
  rw [hnc] at hZQ
  have hne : (i : ι) ≠ n i := fun he => (he ▸ hlt).false
  obtain ⟨hau,hbv,hleft,hright,hp,hq,hu,hv⟩ :=
    original_rectangle_edge_gaps F hRF.injective (c i) (ha i).1 (hb i).1
      (ha (n i)).1 (hb (n i)).1 (hdis hne) hMQ hMT hDQ hZQ
  refine ⟨hnc,hlt,hbv,hM,hMQ,hMT,hcomp,?_,G,hG,hGW,hGZ,?_,?_⟩
  · intro side
    obtain ⟨heK,hes,he2⟩ := originalRectangleEdge_original_face K hs F hRF.injective hverts (c i) side
    refine ⟨originalRectangleEdge_injective F hRF.injective (c i) side,heK,hes,he2,?_⟩
    cases side
    · exact ⟨hbv,hleft,hp,hu⟩
    · exact ⟨hau,hright,hq,hv⟩
  · simpa only [originalRectangleEdge_image,Bool.false_eq_true,if_false] using hGL
  · simpa only [originalRectangleEdge_image,if_true] using hGR

end PoincareConjecture.M76.PrismBelt
