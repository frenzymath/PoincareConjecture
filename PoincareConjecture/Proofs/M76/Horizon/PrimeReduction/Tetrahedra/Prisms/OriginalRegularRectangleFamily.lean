import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.RegularFaceRegionLabels

set_option autoImplicit false
universe u
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem exists_original_regular_rectangle_family
    {E : Type*} {ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [Finite ι]
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (d r : ι → Set E) (hd : ∀ i, IsFinitePLBallPair ℝ (d i) (r i))
    (hsub : ∀ i, d i ⊆ convexHull ℝ (s : Set E))
    (hrim : ∀ i, r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    (hdis : Pairwise fun i j => Disjoint (d i) (d j))
    (hvertex : ∀ i, Disjoint (d i) (s : Set E))
    (hnr : ∀ i, ∀ t : Finset E, t ⊆ s → t.card = 2 → ¬ r i ⊆ convexHull ℝ (t : Set E)) :
    ∃ (κ : Type u) (_ : Finite κ) (M : κ → Set E) (arcs : κ → Bool → ι)
      (edge : κ → Bool → ℝ →ᴬ[ℝ] E) (lo hi : κ → Bool → ℝ)
      (exceptional : Set (ConnectedComponents (convexHull ℝ (s : Set E) \ ⋃ i, d i : Set E))),
      Function.Injective M ∧ exceptional.Finite ∧ exceptional.ncard ≤ 4 ∧
      (∀ x : (convexHull ℝ (s : Set E) \ ⋃ i, d i : Set E),
        ConnectedComponents.mk x ∉ exceptional ↔ ∃! k, (x : E) ∈ M k \ ⋃ i, d i) ∧
      ∀ k, arcs k false ≠ arcs k true ∧
        IsFinitePLBallPair (ℝ × ℝ) (M k)
          ((d (arcs k false) ∪ d (arcs k true)) ∪
            ((edge k false '' Icc (lo k false) (hi k false)) ∪
              (edge k true '' Icc (lo k true) (hi k true)))) ∧
        M k ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) =
          ((edge k false '' Icc (lo k false) (hi k false)) ∪
            (edge k true '' Icc (lo k true) (hi k true))) ∧
        M k ∩ (⋃ i, d i) = d (arcs k false) ∪ d (arcs k true) ∧
        (∀ x ∈ M k \ ⋃ i, d i,
          x ∈ convexHull ℝ (s : Set E) \ ⋃ i, d i ∧
          closure (connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ i, d i) x) = M k) ∧
        (∀ side : Bool, Function.Injective (edge k side) ∧
          ({edge k side 0,edge k side 1} : Finset E) ∈ K.faces ∧
          ({edge k side 0,edge k side 1} : Finset E) ⊆ s ∧
          ({edge k side 0,edge k side 1} : Finset E).card = 2 ∧
          lo k side ∈ Ioo (0 : ℝ) 1 ∧ hi k side ∈ Ioo (0 : ℝ) 1 ∧ lo k side < hi k side ∧
          Disjoint (edge k side '' Ioo (lo k side) (hi k side)) (⋃ i, d i) ∧
          edge k side (lo k side) ∈ ⋃ i, d i ∧ edge k side (hi k side) ∈ ⋃ i, d i) ∧
        ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M k,
          G.IsFinitePL ∧
          (∀ x, (G x : E) ∈ d (arcs k false) ↔ (x : ℝ × ℝ).2 = 0) ∧
          (∀ x, (G x : E) ∈ d (arcs k true) ↔ (x : ℝ × ℝ).2 = 1) ∧
          (∀ x, (G x : E) ∈ edge k false '' Icc (lo k false) (hi k false) ↔ (x : ℝ × ℝ).1 = 0) ∧
          (∀ x, (G x : E) ∈ edge k true '' Icc (lo k true) (hi k true) ↔ (x : ℝ × ℝ).1 = 1) := by
  classical
  obtain ⟨F,c,a,b,hFi,hverts,hface,ha,hb,hcard,hbound,n,M,hMi,hdata⟩ :=
    exists_original_face_edge_gap_family K hs hs3 d r hd hsub hrim hdis hvertex hnr
  let κ := {i : ι // ∃ j, c j = c i ∧ a i < a j}
  have hcut (k : κ) := (hdata k).2.2.2.2.2.1
  have hcomp (k : κ) := (hdata k).2.2.2.2.2.2.1
  have hcharts (k : κ) := (hdata k).2.2.2.2.2.2.2.2
  obtain ⟨exceptional,hexFin,hexCard,hlabels,hactual⟩ :=
    exists_original_face_rectangle_exceptions K hs hs3 d r hd hsub hrim hdis M
      (fun k => d k) (fun k => d (n k)) hMi hcut hcomp
      (fun k => by obtain ⟨G,hG,hW,hZ,_⟩ := hcharts k; exact ⟨G,hW,hZ⟩) hcard hbound
  let arcs (k : κ) (side : Bool) := if side then n k else (k : ι)
  let edge (k : κ) (side : Bool) := originalRectangleEdge F (c k) side
  let lo (k : κ) (side : Bool) := if side then a k else b k
  let hi (k : κ) (side : Bool) := if side then a (n k) else b (n k)
  refine ⟨κ,inferInstance,M,arcs,edge,lo,hi,exceptional,hMi,hexFin,hexCard,hlabels,?_⟩
  intro k
  obtain ⟨hnc,hlt,hbv,hM,hMQ,hMT,hcomp',hgap,G,hG,hW,hZ,hL,hR⟩ := hdata k
  have hedge : F '' (TriangleCorner.cornerMap (c k) ''
      TriangleCorner.edgeIntervals (a k) (b k) (a (n k)) (b (n k))) =
      (edge k false '' Icc (lo k false) (hi k false)) ∪
        (edge k true '' Icc (lo k true) (hi k true)) := by
    simp only [edge,lo,hi,originalRectangleEdge_image,Bool.false_eq_true,if_false,if_true,
      TriangleCorner.edgeIntervals,image_union]
  have hne : arcs k false ≠ arcs k true := by
    change (k : ι) ≠ n k
    exact fun he => (he ▸ hlt).false
  refine ⟨hne,?_,hMQ.trans hedge,hMT,hactual k,?_,G,hG,hW,hZ,hL,hR⟩
  · change IsFinitePLBallPair (ℝ × ℝ) (M k) ((d k ∪ d (n k)) ∪ _)
    rw [←hedge,union_assoc]
    exact hM
  · intro side
    obtain ⟨hei,heK,hes,he2,hlohi,havoid,hloT,hhiT⟩ := hgap side
    refine ⟨hei,heK,hes,he2,?_,?_,hlohi,havoid,hloT,hhiT⟩
    · cases side
      · exact hb k
      · exact ha k
    · cases side
      · exact hb (n k)
      · exact ha (n k)

end PoincareConjecture.M76.PrismBelt
