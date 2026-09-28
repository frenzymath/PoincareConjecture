import PoincareConjecture.Proofs.M76.Mathlib.GeometricCyclePolygons
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle
import PoincareConjecture.Proofs.M76.Mathlib.ClosedRegionPatchIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.LinkGraphIncidence
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph








set_option autoImplicit false

open Set Geometry Topology
open scoped Topology

namespace PoincareConjecture.M76.Dehn.Annuli

open Classical in
theorem exists_paired_polygon_components
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {f : E → X}
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite) (hGS : G.space ⊆ S)
    (hcard : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (partner : G.space ≃ₜ G.space) (hp : partner.IsFinitePL)
    (hp2 : Function.Involutive partner)
    (hpvalue : ∀ x : G.space, f (partner x) = f x)
    (hpunique : ∀ (x : G.space) (y : E), y ∈ S → (x : E) ≠ y →
      f x = f y → y = (partner x : E)) :
    ∃ (n : G.vertexAbstractComplex.edgeGraph.ConnectedComponent → ℕ)
      (P : ∀ A, Polygon E (n A + 3))
      (mate : Equiv.Perm G.vertexAbstractComplex.edgeGraph.ConnectedComponent),
      Finite G.vertexAbstractComplex.edgeGraph.ConnectedComponent ∧
      (∀ A, Function.Injective (P A) ∧ (P A).HasSimplicialEdges ∧
        (P A).boundary ℝ =
          A.toSimpleGraph.segmentCarrier (fun v ↦ (v.val : E))) ∧
      G.space = ⋃ A, (P A).boundary ℝ ∧
      Pairwise (fun A B ↦ Disjoint ((P A).boundary ℝ) ((P B).boundary ℝ)) ∧
      (∀ A, IsCompact ((P A).boundary ℝ) ∧ IsConnected ((P A).boundary ℝ) ∧
        IsClopen ((Subtype.val : G.space → E) ⁻¹' (P A).boundary ℝ)) ∧
      Function.Involutive mate ∧
      (∀ A (x : G.space), (x : E) ∈ (P A).boundary ℝ ↔
        (partner x : E) ∈ (P (mate A)).boundary ℝ) ∧
      (∀ A, f '' (P (mate A)).boundary ℝ = f '' (P A).boundary ℝ) ∧
      ∀ A B, A ≠ B → mate A ≠ B →
        Disjoint (f '' (P A).boundary ℝ) (f '' (P B).boundary ℝ) := by
  classical
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  let Γ := G.vertexAbstractComplex.edgeGraph
  let pieces := fun A : Γ.ConnectedComponent ↦
    A.toSimpleGraph.segmentCarrier (fun v ↦ (v.val : E))
  have hedge {v w : G.vertices} (hvw : Γ.Adj v w) :
      ({(v : E), (w : E)} : Finset E) ∈ G.faces := by
    have h := hvw.2
    change ({v, w} : Finset G.vertices).map (Function.Embedding.subtype _) ∈ G.faces at h
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
      using h
  have hinter {v w a b : G.vertices} (hvw : Γ.Adj v w) (hab : Γ.Adj a b) :
      segment ℝ (v : E) (w : E) ∩ segment ℝ (a : E) (b : E) ⊆
        convexHull ℝ (({(v : E), (w : E)} : Set E) ∩ {(a : E), (b : E)}) := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      G.inter_subset_convexHull (hedge hvw) (hedge hab)
  have hpositive (v : G.vertices) : 0 < (Γ.neighborSet v).ncard := by
    change 0 < (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard
    rw [hdegree]
    norm_num
  have hcarrier : Γ.segmentCarrier (Subtype.val : G.vertices → E) = G.space := by
    apply subset_antisymm
    · rintro x ⟨v, w, hvw, hx⟩
      exact G.convexHull_subset_space (hedge hvw)
        (by simpa only [Finset.coe_pair, convexHull_pair] using hx)
    · intro x hx
      obtain ⟨face, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hx
      have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces hf)
      rcases (show face.card = 1 ∨ face.card = 2 by have := hcard face hf; omega) with h1 | h2
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
        have hxv : x = v := by
          simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hxf
        subst x
        obtain ⟨w, hvw⟩ := (Set.ncard_pos (Set.toFinite (Γ.neighborSet ⟨v, hf⟩))).mp
          (hpositive ⟨v, hf⟩)
        exact ⟨⟨v, hf⟩, w, hvw, left_mem_segment ℝ _ _⟩
      · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp h2
        have hv := G.face_subset_vertices hf (Finset.mem_insert_self _ _)
        have hw := G.face_subset_vertices hf (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _))
        have hadj : Γ.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
          refine ⟨fun h => hvw (congrArg Subtype.val h), ?_⟩
          change ({(⟨v, hv⟩ : G.vertices), ⟨w, hw⟩} : Finset G.vertices).map
            (Function.Embedding.subtype _) ∈ G.faces
          simpa only [Finset.map_insert, Finset.map_singleton,
            Function.Embedding.coe_subtype] using hf
        exact ⟨⟨v, hv⟩, ⟨w, hw⟩, hadj,
          by simpa only [Finset.coe_pair, convexHull_pair] using hxf⟩
  have hcover : G.space = ⋃ A, pieces A :=
    hcarrier.symm.trans (Γ.segmentCarrier_eq_iUnion_components _)
  have hsub (A : Γ.ConnectedComponent) : pieces A ⊆ G.space :=
    fun _ hx => hcover.symm.subset (mem_iUnion.mpr ⟨A, hx⟩)
  have hdisj : Pairwise (fun A B => Disjoint (pieces A) (pieces B)) :=
    Γ.pairwise_disjoint_component_segmentCarrier _ Subtype.val_injective
      (fun {_ _ _ _} h h' => hinter h h')
  have hsame {A B : Γ.ConnectedComponent} {x : E}
      (hx : x ∈ pieces A) (hy : x ∈ pieces B) : A = B := by
    by_contra h
    exact disjoint_left.mp (hdisj h) hx hy
  obtain ⟨n, P, hP, _, _⟩ := Γ.exists_component_polygons_of_two_neighbors
    (Subtype.val : G.vertices → E) hdegree Subtype.val_injective
      (fun {_ _ _ _} h h' ↦ hinter h h')
  have hPs (A : Γ.ConnectedComponent) : (P A).boundary ℝ = pieces A := (hP A).2.2
  have htop (A : Γ.ConnectedComponent) : IsCompact (pieces A) ∧ IsConnected (pieces A) := by
    obtain ⟨eP⟩ := (P A).nonempty_boundary_homeomorph_circle (hP A).2.1 (hP A).1
    have hc : IsConnected ((P A).boundary ℝ) := isConnected_iff_connectedSpace.mpr
      (eP.connectedSpace_iff.mpr inferInstance)
    exact ⟨hPs A ▸ (P A).isCompact_boundary, hPs A ▸ hc⟩
  have hclopen (A : Γ.ConnectedComponent) :
      IsClopen ((Subtype.val : G.space → E) ⁻¹' pieces A) := by
    have hc : IsClosed ((Subtype.val : G.space → E) ⁻¹' pieces A) :=
      (htop A).1.isClosed.preimage continuous_subtype_val
    have hcompl : ((Subtype.val : G.space → E) ⁻¹' pieces A)ᶜ =
        ⋃ B : {B : Γ.ConnectedComponent // B ≠ A},
          (Subtype.val : G.space → E) ⁻¹' pieces B.val := by
      ext x
      constructor
      · intro hx
        obtain ⟨B, hxB⟩ := mem_iUnion.mp (hcover.subset x.property)
        exact mem_iUnion.mpr ⟨⟨B, fun h => hx (h ▸ hxB)⟩, hxB⟩
      · rintro hx hxA
        obtain ⟨B, hxB⟩ := mem_iUnion.mp hx
        exact B.property (hsame hxB hxA)
    refine ⟨hc, isClosed_compl_iff.mp ?_⟩
    rw [hcompl]
    exact isClosed_iUnion_of_finite fun B =>
      (htop B.val).1.isClosed.preimage continuous_subtype_val
  obtain ⟨sigma, hsigma, hsigmaval⟩ := hp
  have hsigmaG {x : E} (hx : x ∈ G.space) : sigma x ∈ G.space := by
    rw [← hsigmaval ⟨x, hx⟩]
    exact (partner ⟨x, hx⟩).property
  have hsigma2 {x : E} (hx : x ∈ G.space) : sigma (sigma x) = x := by
    rw [← hsigmaval ⟨x, hx⟩, ← hsigmaval (partner ⟨x, hx⟩)]
    exact congrArg Subtype.val (hp2 ⟨x, hx⟩)
  have hmate : ∀ A : Γ.ConnectedComponent, ∃ B, sigma '' pieces A ⊆ pieces B := by
    intro A
    have hc := (htop A).2.image sigma (hsigma.continuousOn.mono (hsub A))
    obtain ⟨B, hB⟩ := hc.exists_closure_subset_of_finite_closed_cover pieces
      (fun B => (htop B).1.isClosed)
      (by rintro _ ⟨x, hx, rfl⟩; exact hcover.subset (hsigmaG (hsub A hx)))
      (g := ∅) (fun A B hAB => (disjoint_iff_inter_eq_empty.mp (hdisj hAB)).subset)
      (disjoint_empty _)
    exact ⟨B, subset_closure.trans hB⟩
  choose mate hmate using hmate
  have hmate2 (A : Γ.ConnectedComponent) : mate (mate A) = A := by
    obtain ⟨x, hx⟩ := (htop A).2.nonempty
    have h1 := hmate A (mem_image_of_mem sigma hx)
    have h2 := hmate (mate A) (mem_image_of_mem sigma h1)
    rw [hsigma2 (hsub A hx)] at h2
    exact hsame h2 hx
  let perm : Equiv.Perm Γ.ConnectedComponent :=
    { toFun := mate, invFun := mate, left_inv := hmate2, right_inv := hmate2 }
  have hmem (A : Γ.ConnectedComponent) (x : G.space) :
      (x : E) ∈ pieces A ↔ (partner x : E) ∈ pieces (perm A) := by
    rw [hsigmaval]
    constructor
    · exact fun hx => hmate A (mem_image_of_mem sigma hx)
    · intro hx
      have h := hmate (mate A) (mem_image_of_mem sigma hx)
      rwa [hmate2, hsigma2 x.property] at h
  have hfsigma {x : E} (hx : x ∈ G.space) : f (sigma x) = f x := by
    rw [← hsigmaval ⟨x, hx⟩]
    exact hpvalue ⟨x, hx⟩
  have himages (A : Γ.ConnectedComponent) : f '' pieces (perm A) = f '' pieces A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxG := hsub (perm A) hx
      have hxA := (hmem A ⟨sigma x, hsigmaG hxG⟩).mpr (by
        rw [hsigmaval, hsigma2 hxG]
        exact hx)
      exact ⟨sigma x, hxA, hfsigma hxG⟩
    · rintro ⟨x, hx, rfl⟩
      have hxG := hsub A hx
      refine ⟨sigma x, ?_, hfsigma hxG⟩
      simpa only [hsigmaval] using (hmem A ⟨x, hxG⟩).mp hx
  have himageDisj (A B : Γ.ConnectedComponent) (hAB : A ≠ B) (hpAB : perm A ≠ B) :
      Disjoint (f '' pieces A) (f '' pieces B) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxG := hsub A hx
    have hzG := hsub B hz
    by_cases hxz : x = z
    · exact hAB (hsame hx (hxz.symm ▸ hz))
    · have heq := hpunique ⟨x, hxG⟩ z (hGS hzG) hxz (hxy.trans hzy.symm)
      exact hpAB (hsame ((hmem A ⟨x, hxG⟩).mp hx) (heq ▸ hz))
  refine ⟨n, P, perm, inferInstance, hP, ?_, ?_, ?_, hmate2, ?_, ?_, ?_⟩
  · simpa only [hPs] using hcover
  · simpa only [hPs] using hdisj
  · intro A
    simpa only [hPs] using ⟨(htop A).1, (htop A).2, hclopen A⟩
  · simpa only [hPs] using hmem
  · simpa only [hPs] using himages
  · simpa only [hPs] using himageDisj

end PoincareConjecture.M76.Dehn.Annuli
