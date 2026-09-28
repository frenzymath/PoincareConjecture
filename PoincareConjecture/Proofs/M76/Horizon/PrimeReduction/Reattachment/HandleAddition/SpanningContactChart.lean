import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningRectangleContacts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningMarkedInsideBlock
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option quotPrecheck false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rect" => (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
local notation "Ends" => (({0,1} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1)
local notation "Corners" => (({0,1} : Set ℝ) ×ˢ ({-1,1} : Set ℝ))
local notation "Sides" => (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ))

private theorem image_diff_of_subsets {A B : Type*} {f : A → B} {s t u : Set A}
    (hf : InjOn f u) (hs : s ⊆ u) (ht : t ⊆ u) :
    f '' (s \ t) = f '' s \ f '' t := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hxt⟩,rfl⟩
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    rintro ⟨z,hz,hzx⟩
    exact hxt (hf (ht hz) (hs hx) hzx ▸ hz)
  · rintro ⟨⟨x,hx,rfl⟩,hxt⟩
    exact ⟨x,⟨hx,fun ht => hxt ⟨x,ht,rfl⟩⟩,rfl⟩

private theorem rectangle_open_ends_image {E : Type*} (r : P2 → E)
    (hr : InjOn r Rect) :
    (r '' Ends \ r '' Corners) =
      ((r '' (({0} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1)) \ {r (0,-1),r (0,1)}) ∪
      ((r '' (({1} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1)) \ {r (1,1),r (1,-1)}) := by
  have he : Ends ⊆ Rect := by
    rintro x ⟨hx,hy⟩
    rcases hx with hx | hx <;> exact ⟨by simp_all,hy⟩
  have hc : Corners ⊆ Rect := by
    rintro x ⟨hx,hy⟩
    simp only [mem_insert_iff,mem_singleton_iff] at hx hy
    refine ⟨?_,?_⟩
    · rcases hx with hx | hx <;> norm_num [hx]
    · rcases hy with hy | hy <;> norm_num [hy]
  have h0 : ({0} ×ˢ Icc (-1 : ℝ) 1 : Set P2) ⊆ Rect := by
    rintro x ⟨hx,hy⟩; exact ⟨by simp_all,hy⟩
  have h1 : ({1} ×ˢ Icc (-1 : ℝ) 1 : Set P2) ⊆ Rect := by
    rintro x ⟨hx,hy⟩; exact ⟨by simp_all,hy⟩
  have hc0 : ({(0,-1),(0,1)} : Set P2) ⊆ Rect := by
    rintro x (rfl | rfl) <;> norm_num
  have hc1 : ({(1,1),(1,-1)} : Set P2) ⊆ Rect := by
    rintro x (rfl | rfl) <;> norm_num
  rw [←image_diff_of_subsets hr he hc,←image_pair r (0,-1) (0,1),←image_pair r (1,1) (1,-1),
    ←image_diff_of_subsets hr h0 hc0,←image_diff_of_subsets hr h1 hc1,←image_union]
  congr 1
  ext ⟨x,y⟩
  simp only [mem_sdiff,mem_prod,mem_insert_iff,mem_singleton_iff,mem_union,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx,hy⟩,hn⟩
    rcases hx with h | h
    · exact Or.inl ⟨⟨h,hy⟩,by tauto⟩
    · exact Or.inr ⟨⟨h,hy⟩,by tauto⟩
  · rintro (⟨⟨h,hy⟩,hn⟩ | ⟨⟨h,hy⟩,hn⟩)
    · exact ⟨⟨Or.inl h,hy⟩,by tauto⟩
    · exact ⟨⟨Or.inr h,hy⟩,by tauto⟩

private theorem preconnected_subset_polygon_image_of_mem
    {X I : Type*} [TopologicalSpace X] [T2Space X] [Finite I]
    {s : Set P2} (p : P2 → X) (hp : ContinuousOn p s) (hpi : InjOn p s)
    (n : I → ℕ) (P : ∀ k,Polygon P2 (n k+3))
    (hPs : ∀ k,(P k).boundary ℝ ⊆ s)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    {A : Set X} (hA : IsPreconnected A) (hAs : A ⊆ p '' (⋃ k,(P k).boundary ℝ))
    (i : I) (hi : (A ∩ p '' (P i).boundary ℝ).Nonempty) : A ⊆ p '' (P i).boundary ℝ := by
  classical
  let T (k : I) := p '' (P k).boundary ℝ
  have hT (k : I) : IsClosed (T k) :=
    ((P k).isCompact_boundary.image_of_continuousOn (hp.mono (hPs k))).isClosed
  have hd : Pairwise fun i j => Disjoint (T i) (T j) := by
    intro a b hab
    apply disjoint_left.mpr
    rintro y ⟨x,hx,rfl⟩ ⟨z,hz,hzx⟩
    exact disjoint_left.mp (hdis hab) hx ((hpi (hPs b hz) (hPs a hx) hzx) ▸ hz)
  let V := ⋃ k : {k : I // k ≠ i},T k
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun k => hT k)
  have hAV : A ⊆ T i ∪ V := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hAs hy
    obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    by_cases hki : k = i
    · exact Or.inl ⟨z,hki ▸ hk,rfl⟩
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k,hki⟩,z,hk,rfl⟩)
  intro y hy
  by_contra hni
  have hyV : y ∈ V := (hAV hy).resolve_left hni
  obtain ⟨z,_,hzT,hzV⟩ := isPreconnected_closed_iff.mp hA (T i) V (hT i) hV hAV hi ⟨y,hy,hyV⟩
  obtain ⟨k,hk⟩ := mem_iUnion.mp hzV
  exact disjoint_left.mp (hd (Ne.symm k.property)) hzT hk

theorem exists_spanning_contact_graph_in_original_chart
    {X α I : Type*} [TopologicalSpace X] [T2Space X] [Finite I]
    {e : α → OpenPartialHomeomorph X V3}
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ a,(e a).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {s : Set P2} (p : P2 → X) (hp : PolyhedralPLInCharts e p s)
    (hpi : InjOn p s) (hpQ : MapsTo p s Q.source)
    (n : I → ℕ) (P : ∀ k,Polygon P2 (n k+3))
    (hP : ∀ k,Function.Injective (P k) ∧ (P k).HasSimplicialEdges)
    (hPs : ∀ k,(P k).boundary ℝ ⊆ s)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    {C C' : Set X} (hC : p '' (⋃ k,(P k).boundary ℝ) = C)
    (G : SimplicialComplex ℝ V3) (hG : G.space = Q '' C)
    (i j : I) (hij : i ≠ j) (r : P2 → X)
    (hr : PolyhedralPLInCharts e r Rect) (hri : InjOn r Rect)
    (hrQ : MapsTo r Rect Q.source)
    (htrace : r '' Rect ∩ C = r '' Ends)
    (hleft0 : r (0,0) ∈ p '' (P i).boundary ℝ)
    (hright0 : r (1,0) ∈ p '' (P j).boundary ℝ)
    (hnew : C' = (C \ (r '' Ends \ r '' Corners)) ∪ r '' Sides) :
    ∃ G' : SimplicialComplex ℝ V3,G'.faces.Finite ∧ G'.space = Q '' C' ∧
      HasDisjointPolygonPresentation G'.space ∧
      (∀ a ∈ G'.faces,a.card ≤ 2) ∧
      (∀ x : G'.vertices,(G'.vertexAbstractComplex.edgeGraph.neighborSet x).ncard = 2) ∧
      Nat.card (ConnectedComponents G'.space) + 1 =
        Nat.card (ConnectedComponents G.space) ∧
      Nat.card (ConnectedComponents G'.space) <
        Nat.card (ConnectedComponents G.space) := by
  classical
  have endmember (a : ℝ) (ha : a = 0 ∨ a = 1) (k : I)
      (hk : r (a,0) ∈ p '' (P k).boundary ℝ) :
      r '' ({a} ×ˢ Icc (-1 : ℝ) 1) ⊆ p '' (P k).boundary ℝ := by
    have haR : ({a} ×ˢ Icc (-1 : ℝ) 1 : Set P2) ⊆ Rect := by
      rintro z ⟨hz,ht⟩
      rcases ha with ha | ha <;> exact ⟨by simp_all,ht⟩
    apply preconnected_subset_polygon_image_of_mem p hp.continuousOn hpi n P hPs hdis
      ((isPreconnected_singleton.prod isPreconnected_Icc).image r (hr.continuousOn.mono haR))
      (i := k)
    · rintro y ⟨z,hz,rfl⟩
      apply hC.symm.subset
      apply (htrace.symm.subset ?_).2
      refine ⟨z,⟨?_,hz.2⟩,rfl⟩
      rcases ha with ha | ha <;> simp_all
    · exact ⟨r (a,0),⟨(a,0),by simp,rfl⟩,hk⟩
  have hleft := endmember 0 (Or.inl rfl) i hleft0
  have hright := endmember 1 (Or.inr rfl) j hright0
  have hpoly (k : I) : ∃ (N : ℕ) (T : Polygon V3 (N+3)),Function.Injective T ∧
      T.HasSimplicialEdges ∧ T.boundary ℝ = (Q ∘ p) '' (P k).boundary ℝ := by
    let K := (P k).simplicialComplex (hP k).2
    have hK := (P k).finite_simplicialComplex_faces (hP k).2
    have hKs : K.space = (P k).boundary ℝ := (P k).simplicialComplex_space (hP k).2
    have hpK := hp.restrict_finite K hK (hKs.subset.trans (hPs k))
    have hf := hpK.finitePiecewiseAffineOn_compatible_chart_finite_source K hK Q hQ
      (fun x hx => hpQ (hPs k (hKs.subset hx)))
    apply (P k).exists_polygon_finitePL_image (hP k).2 (hP k).1 hf hKs.symm.subset
    intro x hx y hy hxy
    exact hpi (hPs k hx) (hPs k hy) (Q.injOn (hpQ (hPs k hx)) (hpQ (hPs k hy)) hxy)
  choose N T hTi hTe hTb using hpoly
  have hTd : Pairwise fun i j => Disjoint ((T i).boundary ℝ) ((T j).boundary ℝ) := by
    intro a b hab
    apply disjoint_left.mpr
    rintro y hya hyb
    obtain ⟨x,hx,hxy⟩ := (hTb a).subset hya
    obtain ⟨z,hz,hzy⟩ := (hTb b).subset hyb
    have hxz := hpi (hPs a hx) (hPs b hz)
      (Q.injOn (hpQ (hPs a hx)) (hpQ (hPs b hz)) (hxy.trans hzy.symm))
    exact disjoint_left.mp (hdis hab) hx (hxz.symm ▸ hz)
  have hTC : (⋃ k,(T k).boundary ℝ) = Q '' C := by
    rw [←hC,image_image]
    simp only [hTb,image_iUnion,Function.comp_def]
  have hCQ : C ⊆ Q.source := by
    rintro y hy
    obtain ⟨x,hx,rfl⟩ := hC.symm.subset hy
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx
    exact hpQ (hPs k hk)
  have hRect := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  obtain ⟨K,_,hK,hKs,_,_⟩ := hRect.exists_finite_carrier_and_rim_complexes
  have hrp : FinitePiecewiseAffineOn (Q ∘ r) Rect := by
    rw [←hKs]
    exact (hKs.symm ▸ hr).finitePiecewiseAffineOn_compatible_chart_finite_source K hK Q hQ
      (fun x hx => hrQ (hKs.subset hx))
  have hrpi : InjOn (Q ∘ r) Rect := by
    intro x hx y hy he
    exact hri hx hy (Q.injOn (hrQ hx) (hrQ hy) he)
  have htraceQ : (Q ∘ r) '' Rect ∩ (⋃ k,(T k).boundary ℝ) = (Q ∘ r) '' Ends := by
    rw [hTC]
    simpa only [image_image,Function.comp_def] using
      ((Q.injOn.image_inter hrQ.image_subset hCQ).symm.trans (congrArg (Q '' ·) htrace))
  have hl : (Q ∘ r) '' ({0} ×ˢ Icc (-1 : ℝ) 1) ⊆ (T i).boundary ℝ := by
    rw [hTb i]
    simpa only [image_image,Function.comp_def] using (image_mono hleft : Q '' _ ⊆ Q '' _)
  have hh : (Q ∘ r) '' ({1} ×ˢ Icc (-1 : ℝ) 1) ⊆ (T j).boundary ℝ := by
    rw [hTb j]
    simpa only [image_image,Function.comp_def] using (image_mono hright : Q '' _ ⊆ Q '' _)
  obtain ⟨G',hG',hGs,hpres,hfaces,hdegree,hcount⟩ :=
    exists_spanning_rectangle_contact_graph N T (fun k => ⟨hTi k,hTe k⟩)
      hTd i j hij (Q ∘ r) hrp hrpi htraceQ hl hh
  have heR : Ends ⊆ Rect := by
    rintro x ⟨hx,hy⟩; rcases hx with hx | hx <;> exact ⟨by simp_all,hy⟩
  have hcR : Corners ⊆ Rect := by
    rintro x ⟨hx,hy⟩
    simp only [mem_insert_iff,mem_singleton_iff] at hx hy
    refine ⟨?_,?_⟩
    · rcases hx with hx | hx <;> norm_num [hx]
    · rcases hy with hy | hy <;> norm_num [hy]
  have hside : (Q ∘ r) '' Sides =
      (Q ∘ r) '' (Icc (0 : ℝ) 1 ×ˢ ({1} : Set ℝ)) ∪
      (Q ∘ r) '' (Icc (0 : ℝ) 1 ×ˢ ({-1} : Set ℝ)) := by
    rw [show ({-1,1} : Set ℝ) = {1} ∪ {-1} by ext x; simp [or_comm],prod_union,image_union]
  have himage : Q '' C' = G'.space := by
    rw [hnew,image_union,image_diff_of_subsets Q.injOn hCQ
      (sdiff_subset.trans ((image_mono heR).trans hrQ.image_subset)),
      image_diff_of_subsets Q.injOn ((image_mono heR).trans hrQ.image_subset)
        ((image_mono hcR).trans hrQ.image_subset),image_image,image_image,image_image]
    change Q '' C \ ((Q ∘ r) '' Ends \ (Q ∘ r) '' Corners) ∪ (Q ∘ r) '' Sides = _
    rw [rectangle_open_ends_image (Q ∘ r) hrpi,hside,←hTC]
    exact hGs.symm
  have hcount' : Nat.card (ConnectedComponents G'.space) + 1 =
      Nat.card (ConnectedComponents G.space) := by
    convert hcount using 2
    exact congrArg (fun A : Set V3 => ConnectedComponents A) (hG.trans hTC.symm)
  exact ⟨G',hG',himage.symm,hpres,hfaces,hdegree,hcount',by omega⟩

end PoincareConjecture.M76
