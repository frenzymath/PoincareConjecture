import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.OrdinaryGraph
import PoincareConjecture.Proofs.M76.Mathlib.GeometricPathIntervals
import PoincareConjecture.Proofs.M76.Mathlib.GeometricCyclePolygons
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle
import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundedRegions
import PoincareConjecture.Proofs.M76.Mathlib.ClosedRegionPatchIncidence
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import Mathlib.Topology.Order.IntermediateValue



set_option autoImplicit false
open Set Metric Geometry Topology unitInterval
open scoped Topology

namespace PoincareConjecture.M76.Dehn.Annuli

open Classical in
theorem exists_paired_proper_source_components
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
    {S Q : Set E} {R : Set X}
    (hf : PolyhedralPLInCharts e f S) (hR : MapsTo f S R)
    (hproper : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ Q)
    (G : SimplicialComplex ℝ E) (partner : G.space ≃ₜ G.space)
    (hG : G.faces.Finite) (hGs : G.space = doubleLocusOn f S)
    (hp : partner.IsFinitePL) (hp2 : Function.Involutive partner)
    (hpfree : ∀ x : G.space, partner x ≠ x)
    (hpvalue : ∀ x : G.space, f x = f (partner x))
    (hpunique : ∀ (x : G.space) (y : E), y ∈ S → (x : E) ≠ y →
      f x = f y → y = (partner x : E))
    (hprim : ∀ x : G.space, (partner x : E) ∈ Q ↔ (x : E) ∈ Q)
    (hcard : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        if (v : E) ∈ Q then 1 else 2)
    (hrim : G.space ∩ Q = Subtype.val '' {v : G.vertices |
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1}) :
  ∃ (pieces : G.vertexAbstractComplex.edgeGraph.ConnectedComponent → Set E)
    (mate : Equiv.Perm G.vertexAbstractComplex.edgeGraph.ConnectedComponent),
    Finite G.vertexAbstractComplex.edgeGraph.ConnectedComponent ∧
    (∀ A, pieces A = A.toSimpleGraph.segmentCarrier (fun v => (v.val : E))) ∧
    G.space = ⋃ A, pieces A ∧
    Pairwise (fun A B => Disjoint (pieces A) (pieces B)) ∧
    (∀ A, IsCompact (pieces A) ∧ IsConnected (pieces A) ∧
      IsClopen ((Subtype.val : G.space → E) ⁻¹' pieces A)) ∧
    (∀ A, IsFinitePLBallPair ℝ (pieces A) (pieces A ∩ Q) ∨
      ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
        P.HasSimplicialEdges ∧ P.boundary ℝ = pieces A ∧ Disjoint (pieces A) Q) ∧
    Function.Involutive mate ∧
    (∀ A (x : G.space), (x : E) ∈ pieces A ↔
      (partner x : E) ∈ pieces (mate A)) ∧
    (∀ A, f '' pieces (mate A) =
      f '' pieces A) ∧
    (∀ A B, A ≠ B → mate A ≠ B → Disjoint
      (f '' pieces A)
      (f '' pieces B)) ∧
    ∀ A, IsFinitePLBallPair ℝ (pieces A) (pieces A ∩ Q) →
      mate A ≠ A ∧
      ∃ (alpha : I ≃ₜ pieces A) (beta : I ≃ₜ pieces (mate A)) (arc : ℝ → X),
        alpha.IsFinitePL ∧ beta.IsFinitePL ∧
        (∀ u : I, ∃ hx : (alpha u : E) ∈ G.space,
          (beta u : E) = (partner ⟨alpha u, hx⟩ : E)) ∧
        pieces A ∩ Q = {(alpha 0 : E), (alpha 1 : E)} ∧
        pieces (mate A) ∩ Q = {(beta 0 : E), (beta 1 : E)} ∧
        IsEmbedding (fun u : I => arc u) ∧
        PolyhedralPLInCharts e arc (Icc (0 : ℝ) 1) ∧
        (∀ u : I, arc u = f (alpha u) ∧
          arc u = f (beta u)) ∧
        (∀ x ∈ S, f x ∈
          range (fun u : I => arc u) ↔ x ∈ pieces A ∪ pieces (mate A)) ∧
        (∀ u : I, arc u ∈ frontier R ↔ u = 0 ∨ u = 1) ∧
        ∀ u : I, u ≠ 0 → u ≠ 1 → arc u ∈ interior R := by
  classical
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  let Γ := G.vertexAbstractComplex.edgeGraph
  let pieces := fun A : Γ.ConnectedComponent =>
    A.toSimpleGraph.segmentCarrier (fun v => (v.val : E))
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
    split_ifs <;> norm_num
  have hdegree2 (v : G.vertices) : (Γ.neighborSet v).ncard ≤ 2 := by
    change (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≤ 2
    rw [hdegree]
    split_ifs <;> norm_num
  have hvertex (A : Γ.ConnectedComponent) (v : A) : (v.val : E) ∈ pieces A := by
    obtain ⟨w, hvw⟩ := (Set.ncard_pos (Set.toFinite (Γ.neighborSet v.val))).mp
      (hpositive v.val)
    have hw : w ∈ A.supp := A.mem_supp_of_adj_mem_supp v.property hvw
    exact ⟨v, ⟨w, hw⟩, hvw, left_mem_segment ℝ _ _⟩
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
  have hboundary (A : Γ.ConnectedComponent) : pieces A ∩ Q =
      (fun v : A => (v.val : E)) ''
        {v | (A.toSimpleGraph.neighborSet v).ncard = 1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hvx⟩ := hrim.subset ⟨hsub A hx.1, hx.2⟩
      let B := Γ.connectedComponentMk v
      have hvB : v ∈ B.supp := rfl
      have hBA : B = A := hsame (hvertex B ⟨v, hvB⟩) (hvx.symm ▸ hx.1)
      have hvA : v ∈ A.supp := hBA ▸ hvB
      exact ⟨⟨v, hvA⟩, (A.ncard_neighborSet Γ ⟨v, hvA⟩).trans hv, hvx⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨hvertex A v, ?_⟩
      exact (hrim.symm.subset ⟨v.val,
        (A.ncard_neighborSet Γ v).symm.trans hv, rfl⟩).2
  have hmodels (A : Γ.ConnectedComponent) :
      IsFinitePLBallPair ℝ (pieces A) (pieces A ∩ Q) ∨
        ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
          P.HasSimplicialEdges ∧ P.boundary ℝ = pieces A ∧ Disjoint (pieces A) Q := by
    by_cases hleaf : ∃ v : A, (A.toSimpleGraph.neighborSet v).ncard = 1
    · left
      rw [hboundary]
      exact A.toSimpleGraph.isFinitePLBallPair_segmentCarrier_of_leaf
        (fun v => (v.val : E)) A.connected_toSimpleGraph
        (fun v => (A.ncard_neighborSet Γ v).le.trans (hdegree2 v.val)) hleaf
        (Subtype.val_injective.comp Subtype.val_injective)
        (fun {_ _ _ _} h h' => hinter h h')
    · have htwo (v : A) : (A.toSimpleGraph.neighborSet v).ncard = 2 := by
        have hpv := hpositive v.val
        have hb := hdegree2 v.val
        have heq := A.ncard_neighborSet Γ v
        have hn : (A.toSimpleGraph.neighborSet v).ncard ≠ 1 :=
          fun h => hleaf ⟨v, h⟩
        omega
      obtain ⟨n, P, hPi, hP, hPs⟩ := A.toSimpleGraph.exists_polygon_of_two_neighbors
        (fun v => (v.val : E)) A.connected_toSimpleGraph htwo
        (Subtype.val_injective.comp Subtype.val_injective)
        (fun {_ _ _ _} h h' => hinter h h')
      refine Or.inr ⟨n, P, hPi, hP, hPs, disjoint_iff_inter_eq_empty.mpr ?_⟩
      rw [hboundary]
      apply eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨v, hv, _⟩
      exact hleaf ⟨v, hv⟩
  have htop (A : Γ.ConnectedComponent) : IsCompact (pieces A) ∧ IsConnected (pieces A) := by
    rcases hmodels A with hball | ⟨n, P, hPi, hP, hPs, _⟩
    · exact ⟨hball.isCompact, hball.isConnected⟩
    · obtain ⟨eP⟩ := P.nonempty_boundary_homeomorph_circle hP hPi
      have hc : IsConnected (P.boundary ℝ) := isConnected_iff_connectedSpace.mpr
        (eP.connectedSpace_iff.mpr inferInstance)
      exact ⟨hPs ▸ P.isCompact_boundary, hPs ▸ hc⟩
  have htri (A : Γ.ConnectedComponent) : ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.space = pieces A := by
    rcases hmodels A with hball | ⟨n, P, _hPi, hP, hPs, _⟩
    · obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
      exact ⟨K, hK, hKs⟩
    · exact ⟨P.simplicialComplex hP, P.finite_simplicialComplex_faces hP,
        (P.simplicialComplex_space hP).trans hPs⟩
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
  have hrestrict (A : Γ.ConnectedComponent) :
      (partner.restrictSubsets (hsub A) (hsub (perm A)) (hmem A)).IsFinitePL := by
    obtain ⟨K, hK, hKs⟩ := htri A
    exact (show partner.IsFinitePL from ⟨sigma, hsigma, hsigmaval⟩).restrictSubsets
      (hsub A) (hsub (perm A)) (hmem A) K hK hKs
  have hlowersigma {x : E} (hx : x ∈ G.space) : f (sigma x) = f x := by
    rw [← hsigmaval ⟨x, hx⟩]
    exact (hpvalue ⟨x, hx⟩).symm
  have himages (A : Γ.ConnectedComponent) : f '' pieces (perm A) = f '' pieces A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxG := hsub (perm A) hx
      have hxA := (hmem A ⟨sigma x, hsigmaG hxG⟩).mpr (by
        rw [hsigmaval, hsigma2 hxG]
        exact hx)
      exact ⟨sigma x, hxA, hlowersigma hxG⟩
    · rintro ⟨x, hx, rfl⟩
      have hxG := hsub A hx
      refine ⟨sigma x, ?_, hlowersigma hxG⟩
      simpa only [hsigmaval] using (hmem A ⟨x, hxG⟩).mp hx
  have himageDisj (A B : Γ.ConnectedComponent) (hAB : A ≠ B) (hpAB : perm A ≠ B) :
      Disjoint (f '' pieces A) (f '' pieces B) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxG := hsub A hx
    have hzG := hsub B hz
    by_cases hxz : x = z
    · exact hAB (hsame hx (hxz.symm ▸ hz))
    · have heq := hpunique ⟨x, hxG⟩ z (hGs.subset hzG).1 hxz (hxy.trans hzy.symm)
      exact hpAB (hsame ((hmem A ⟨x, hxG⟩).mp hx) (heq ▸ hz))
  refine ⟨pieces, perm, inferInstance, fun _ => rfl, hcover, hdisj,
    fun A => ⟨(htop A).1, (htop A).2, hclopen A⟩,
    hmodels, hmate2, hmem, himages, himageDisj, ?_⟩
  intro A hball
  obtain ⟨a, b, hab, habound⟩ := hball.exists_boundary_eq_pair
  have hball' : IsFinitePLBallPair ℝ (pieces A) {a, b} := by
    simpa only [habound] using hball
  obtain ⟨alpha, halpha, halpha0, halpha1⟩ := hball'.exists_unitInterval_chart_with_endpoints hab
  let d := partner.restrictSubsets (hsub A) (hsub (perm A)) (hmem A)
  have hd : d.IsFinitePL := hrestrict A
  have hne : perm A ≠ A := by
    intro heq
    have hm : ∀ x : G.space, (x : E) ∈ pieces A ↔ (partner x : E) ∈ pieces A := by
      intro x
      simpa only [heq] using hmem A x
    let d0 := partner.restrictSubsets (hsub A) (hsub A) hm
    obtain ⟨K, hK, hKs⟩ := htri A
    have hd0 : d0.IsFinitePL :=
      (show partner.IsFinitePL from ⟨sigma, hsigma, hsigmaval⟩).restrictSubsets
        (hsub A) (hsub A) hm K hK hKs
    let e0 := alpha.trans (d0.trans alpha.symm)
    obtain ⟨F, hF, hFval⟩ := halpha.trans (hd0.trans halpha.symm)
    have hFI : MapsTo F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro x hx
      rw [← hFval ⟨x, hx⟩]
      exact (e0 ⟨x, hx⟩).property
    obtain ⟨x, hx, hFx⟩ := exists_mem_Icc_isFixedPt_of_mapsTo
      hF.continuousOn zero_le_one hFI
    have he0 : e0 ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext ((hFval ⟨x, hx⟩).trans hFx)
    have hd0fix : d0 (alpha ⟨x, hx⟩) = alpha ⟨x, hx⟩ := by
      have h := congrArg alpha he0
      change alpha (alpha.symm (d0 (alpha ⟨x, hx⟩))) = alpha ⟨x, hx⟩ at h
      simpa only [alpha.apply_symm_apply] using h
    exact hpfree ⟨alpha ⟨x, hx⟩, hsub A (alpha ⟨x, hx⟩).property⟩
      (Subtype.ext (congrArg (fun y : pieces A => (y : E)) hd0fix))
  let beta := alpha.trans d
  have hbeta : beta.IsFinitePL := halpha.trans hd
  have hbetaval (u : I) : (beta u : E) =
      (partner ⟨alpha u, hsub A (alpha u).property⟩ : E) := rfl
  have halpharim : pieces A ∩ Q = {(alpha 0 : E), (alpha 1 : E)} := by
    have h0 : (alpha (0 : I) : E) = a := halpha0
    have h1 : (alpha (1 : I) : E) = b := halpha1
    rw [h0, h1]
    exact habound
  have hbetarim : pieces (perm A) ∩ Q = {(beta 0 : E), (beta 1 : E)} := by
    ext x
    constructor
    · intro hx
      let y : pieces A := d.symm ⟨x, hx.1⟩
      have hdx : (d y : E) = x := congrArg Subtype.val (d.apply_symm_apply ⟨x, hx.1⟩)
      have hyr : (y : E) ∈ Q := (hprim ⟨y, hsub A y.property⟩).mp (hdx.symm ▸ hx.2)
      rcases halpharim.subset ⟨y.property, hyr⟩ with h0 | h1
      · exact Or.inl (hdx.symm.trans (congrArg (fun z : pieces A => (d z : E))
          (Subtype.ext h0)))
      · exact Or.inr (hdx.symm.trans (congrArg (fun z : pieces A => (d z : E))
          (Subtype.ext h1)))
    · rintro (rfl | rfl)
      · exact ⟨(beta 0).property, (hprim ⟨alpha 0, hsub A (alpha 0).property⟩).mpr
          (halpharim.symm.subset (Or.inl rfl)).2⟩
      · exact ⟨(beta 1).property, (hprim ⟨alpha 1, hsub A (alpha 1).property⟩).mpr
          (halpharim.symm.subset (Or.inr rfl)).2⟩
  obtain ⟨l, hl, hlval⟩ := halpha
  have hlD : MapsTo l (Icc (0 : ℝ) 1) S := by
    intro u hu
    rw [← hlval ⟨u, hu⟩]
    exact (hGs.subset (hsub A (alpha ⟨u, hu⟩).property)).1
  let arc := f ∘ l
  have harc (u : I) : arc u = f (alpha u) := congrArg f (hlval u).symm
  have hsync (u : I) : arc u = f (beta u) :=
    (harc u).trans (hpvalue ⟨alpha u, hsub A (alpha u).property⟩)
  have harcPL : PolyhedralPLInCharts e arc (Icc (0 : ℝ) 1) := by
    obtain ⟨K, hK, hKs, hlaff⟩ := hl
    have h := hf.comp_finitePiecewiseAffineOn K hK
      (show FinitePiecewiseAffineOn l K.space from
        ⟨K, hK, rfl, hlaff⟩) (by simpa only [hKs] using hlD)
    simpa only [hKs] using h
  have harci : Function.Injective (fun u : I => arc u) := by
    intro u v huv
    have huG := hsub A (alpha u).property
    have hvG := hsub A (alpha v).property
    by_cases heq : (alpha u : E) = (alpha v : E)
    · exact alpha.injective (Subtype.ext heq)
    · have hval : f (alpha u) = f (alpha v) := (harc u).symm.trans (huv.trans (harc v))
      have h := hpunique ⟨alpha u, huG⟩ (alpha v) (hGs.subset hvG).1 heq hval
      exact (disjoint_left.mp (hdisj hne) ((hmem A ⟨alpha u, huG⟩).mp (alpha u).property)
        (h ▸ (alpha v).property)).elim
  have harcEmbedding : IsEmbedding (fun u : I => arc u) :=
    (harcPL.continuousOn.domRestrict.isClosedEmbedding harci).isEmbedding
  have hpreimage (x : E) (hx : x ∈ S) : f x ∈ range (fun u : I => arc u) ↔
      x ∈ pieces A ∪ pieces (perm A) := by
    constructor
    · rintro ⟨u, hu⟩
      by_cases hxu : (alpha u : E) = x
      · exact Or.inl (hxu ▸ (alpha u).property)
      · have hval : f (alpha u) = f x := (harc u).symm.trans hu
        have h := hpunique ⟨alpha u, hsub A (alpha u).property⟩ x hx hxu hval
        exact Or.inr (h.symm ▸ (hmem A ⟨alpha u, hsub A (alpha u).property⟩).mp (alpha u).property)
    · rintro (hxA | hxB)
      · refine ⟨alpha.symm ⟨x, hxA⟩, ?_⟩
        change arc (alpha.symm ⟨x, hxA⟩) = f x
        rw [harc, alpha.apply_symm_apply]
      · refine ⟨beta.symm ⟨x, hxB⟩, ?_⟩
        change arc (beta.symm ⟨x, hxB⟩) = f x
        rw [hsync, beta.apply_symm_apply]
  have hproper (u : I) : arc u ∈ frontier R ↔ u = 0 ∨ u = 1 := by
    have hxD := (hGs.subset (hsub A (alpha u).property)).1
    have ht : f (alpha u) ∈ frontier R ↔ (alpha u : E) ∈ Q :=
      hproper _ hxD
    rw [harc]
    change f (alpha u) ∈ frontier R ↔ _
    rw [ht]
    constructor
    · intro hu
      rcases halpharim.subset ⟨(alpha u).property, hu⟩ with h0 | h1
      · exact Or.inl (alpha.injective (Subtype.ext h0))
      · exact Or.inr (alpha.injective (Subtype.ext h1))
    · rintro (rfl | rfl)
      · exact (halpharim.symm.subset (Or.inl rfl)).2
      · exact (halpharim.symm.subset (Or.inr rfl)).2
  refine ⟨hne, alpha, beta, arc, ⟨l, hl, hlval⟩, hbeta,
    fun u => ⟨hsub A (alpha u).property, hbetaval u⟩, halpharim, hbetarim,
    harcEmbedding, harcPL, fun u => ⟨harc u, hsync u⟩, hpreimage, hproper, ?_⟩
  intro u hu0 hu1
  have hxD := (hGs.subset (hsub A (alpha u).property)).1
  have hin : arc u ∈ R := by
    rw [harc]
    exact hR hxD
  have hn : arc u ∉ frontier R := by
    rw [hproper]
    exact not_or.mpr ⟨hu0, hu1⟩
  exact (closure_sdiff_frontier R).subset ⟨subset_closure hin, hn⟩

end PoincareConjecture.M76.Dehn.Annuli
