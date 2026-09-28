import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.PhysicalEdgeGapMatching

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
open TriangleCorner

theorem mem_open_interval_image_of_noncut
    {E : Type*} (e : ℝ → E) {T : Set E} {a b : ℝ} {x : E}
    (ha : e a ∈ T) (hb : e b ∈ T) (hx : x ∈ e '' Icc a b) (hxT : x ∉ T) :
    x ∈ e '' Ioo a b := by
  obtain ⟨t,ht,rfl⟩ := hx
  refine ⟨t,⟨lt_of_le_of_ne ht.1 ?_,lt_of_le_of_ne ht.2 ?_⟩,rfl⟩
  · intro he
    subst t
    exact hxT ha
  · intro he
    subst t
    exact hxT hb

theorem exists_matching_neighbor_rectangle_side
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s u : Finset E} (hs : s ∈ K.faces) (hu : u ∈ K.faces)
    {T V M D Z : Set E} {S : Set X}
    (hT : T ⊆ convexHull ℝ (s : Set E)) (hV : V ⊆ convexHull ℝ (u : Set E))
    (hphysicalT : g '' T = S ∩ (g '' convexHull ℝ (s : Set E)))
    (hphysicalV : g '' V = S ∩ (g '' convexHull ℝ (u : Set E)))
    (e : ℝ →ᴬ[ℝ] E) (he : Function.Injective e)
    (heK : ({e 0,e 1} : Finset E) ∈ K.faces)
    (hes : ({e 0,e 1} : Finset E) ⊆ s)
    {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hhi1 : hi ≤ 1)
    (hlo : e lo ∈ T) (hhi : e hi ∈ T) (hgap : Disjoint (e '' Ioo lo hi) T)
    (F : (ℝ × ℝ) →ᴬ[ℝ] E) (hF : Function.Injective F)
    (hverts : F '' vertices = (u : Set E)) (c : Fin 3)
    {a b p q : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hDZ : Disjoint D Z)
    (hMQ : M ∩ intrinsicFrontier ℝ (convexHull ℝ (u : Set E)) =
      F '' (cornerMap c '' edgeIntervals a b p q))
    (hMV : M ∩ V = D ∪ Z)
    (hDQ : D ∩ intrinsicFrontier ℝ (convexHull ℝ (u : Set E)) =
      F '' (cornerMap c '' ({(0,b),(a,0)} : Set (ℝ × ℝ))))
    (hZQ : Z ∩ intrinsicFrontier ℝ (convexHull ℝ (u : Set E)) =
      F '' (cornerMap c '' ({(0,q),(p,0)} : Set (ℝ × ℝ))))
    {x : E} (hx : x ∈ e '' Ioo lo hi)
    (hxM : x ∈ M) (hxQ : x ∈ intrinsicFrontier ℝ (convexHull ℝ (u : Set E))) :
    ∃! side : Bool,
      let f := originalRectangleEdge F c side
      let left := if side then a else b
      let right := if side then p else q
      x ∈ f '' Ioo left right ∧
        ({e 0,e 1} : Finset E) = {f 0,f 1} ∧ e '' Icc lo hi = f '' Icc left right ∧
        g '' (e '' Icc lo hi) = g '' (f '' Icc left right) := by
  obtain ⟨_,_,hglobal⟩ := original_face_edge_gap_to_physical_cut K g hgi hs hT hphysicalT
    e hes hlo0 hhi1 hlo hhi hgap
  have hxV : x ∉ V := by
    intro hxV
    exact disjoint_left.mp hglobal hx (hphysicalV.subset (mem_image_of_mem g hxV)).1
  obtain ⟨hap,hbq,hleft,hright,hleft0,hright0,hleft1,hright1⟩ :=
    original_rectangle_edge_gaps F hF c ha.1 hb.1 hp.1 hq.1 hDZ hMQ hMV hDQ hZQ
  have hboundary : M ∩ intrinsicFrontier ℝ (convexHull ℝ (u : Set E)) =
      (originalRectangleEdge F c false '' Icc b q) ∪
      (originalRectangleEdge F c true '' Icc a p) := by
    simpa only [originalRectangleEdge_image,Bool.false_eq_true,if_false,if_true,
      edgeIntervals,image_union] using hMQ
  have hex : ∃ side : Bool,
      x ∈ originalRectangleEdge F c side ''
        Ioo (if side then a else b) (if side then p else q) := by
    rcases hboundary.subset ⟨hxM,hxQ⟩ with hl | hr
    · exact ⟨false,mem_open_interval_image_of_noncut _ hleft0 hleft1 hl hxV⟩
    · exact ⟨true,mem_open_interval_image_of_noncut _ hright0 hright1 hr hxV⟩
  obtain ⟨side,hside⟩ := hex
  obtain ⟨hfK,hfu,_⟩ := originalRectangleEdge_original_face K hu F hF hverts c side
  have hsidegap : Disjoint (originalRectangleEdge F c side ''
      Ioo (if side then a else b) (if side then p else q)) V := by
    cases side
    · exact hleft
    · exact hright
  have hs0 : originalRectangleEdge F c side (if side then a else b) ∈ V := by
    cases side
    · exact hleft0
    · exact hright0
  have hs1 : originalRectangleEdge F c side (if side then p else q) ∈ V := by
    cases side
    · exact hleft1
    · exact hright1
  have hslo : 0 ≤ if side then a else b := by
    cases side
    · exact hb.1.le
    · exact ha.1.le
  have hshi : (if side then p else q) ≤ 1 := by
    cases side
    · exact hq.2.le
    · exact hp.2.le
  obtain ⟨hedge,hmatch,hphysical⟩ := original_physical_face_edge_gaps_match K g hgi hs hu
    hT hV hphysicalT hphysicalV e (originalRectangleEdge F c side) he
    (originalRectangleEdge_injective F hF c side) heK hfK hes hfu
    hlo0 hhi1 hslo hshi hlo hhi hs0 hs1 hgap hsidegap ⟨x,hx,hside⟩
  refine ⟨side,⟨hside,hedge,hmatch,hphysical⟩,?_⟩
  intro other hother
  have hdis := originalRectangleEdge_sides_disjoint F hF c (b := b) (p := p) (q := q) ha.1
  by_contra hne
  cases side <;> cases other
  · exact hne rfl
  · exact disjoint_left.mp hdis (image_mono Ioo_subset_Icc_self hside)
      (image_mono Ioo_subset_Icc_self hother.1)
  · exact disjoint_left.mp hdis (image_mono Ioo_subset_Icc_self hother.1)
      (image_mono Ioo_subset_Icc_self hside)
  · exact hne rfl

end PoincareConjecture.M76.PrismBelt
