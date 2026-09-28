import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalVertexCoordinateSectors

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem original_interior_vertex_region_eq
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R)
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (v : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z)))
    (hvFr : (g v : X) ∉ frontier R) :
    ((M reg).barycentricDualBlock {(v : E)}).space =
        (K.barycentricDualBlock {(v : E)}).space ∧
      Disjoint (K.barycentricDualBlock {(v : E)}).space (M fr).space ∧
      ∀ z ∈ (K.barycentricDualBlock {(v : E)}).space, (g z : X) ∈ interior R := by
  classical
  let V := K.barycentricDualBlock {(v : E)}
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(v : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hvA : (g v : X) ∈ A := (harc v (K.vertices_subset_space hvK)).mp
    ((M arc).vertices_subset_space v.property)
  have hball := isFinitePLBallPair_original_interior_vertex_dual K H g hg
    hvK (hAC hvA) B hsource hface
  have hvnot : (v : E) ∉ (M fr).vertices := fun h => hvFr
    ((hfr v (K.vertices_subset_space hvK)).mp ((M fr).vertices_subset_space h))
  have hfoot : V.space ∩ (M fr).space = ∅ := by
    rw [K.barycentricDualBlock_space_inter_subcomplex (M fr) (hMK fr) {(v : E)}]
    exact (M fr).barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.singleton_nonempty (v : E)) hvnot
  have hconn := hball.isConnected.isPreconnected.image (fun z => (g z : X))
    (hgPL.continuousOn.mono hVK)
  have havoid : Disjoint (frontier (interior R)) ((fun z => (g z : X)) '' V.space) := by
    apply Set.disjoint_left.mpr
    rintro _ hz ⟨w, hw, rfl⟩
    exact (hfoot.subset ⟨hw, (hfr w (hVK hw)).mpr (frontier_interior_subset hz)⟩).elim
  have hvR : (g v : X) ∈ interior R := by
    by_contra hn
    exact hvFr ⟨subset_closure (hAR hvA), hn⟩
  have hvV : (v : E) ∈ V.space := by
    rw [show V = K.barycentricSubdivision.closedStar v from
      K.barycentricDualBlock_singleton_eq_closedStar hvK]
    apply (K.barycentricSubdivision.closedStar v).vertices_subset_space
    change {(v : E)} ∈ K.barycentricSubdivision.faces ∧
      insert (v : E) {(v : E)} ∈ K.barycentricSubdivision.faces
    have hvJs : {(v : E)} ∈ K.barycentricSubdivision.faces :=
      K.barycentricSubdivision_isSubdivision.vertices_subset hvK
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (v : E)), and_self] using hvJs
  have hinside (z : E) (hz : z ∈ V.space) : (g z : X) ∈ interior R :=
    hconn.m76_subset_of_disjoint_frontier isOpen_interior havoid
      ⟨g v, mem_image_of_mem _ hvV, hvR⟩ (mem_image_of_mem _ hz)
  refine ⟨?_, Set.disjoint_iff_inter_eq_empty.mpr hfoot, hinside⟩
  rw [← K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) {(v : E)}]
  exact inter_eq_left.mpr (fun z hz => (hreg z (hVK hz)).mpr (interior_subset (hinside z hz)))

open Classical in

theorem isFinitePLBallPair_original_interior_sector
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (S : Fin 2 → Set X)
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (v : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z)))
    (haxis : ∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0)
    (hsheets : ∀ i y, y ∈ B.source → (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0))
    (hvFr : (g v : X) ∉ frontier R) (signs : Fin 2 → Bool) :
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let cuts := {z | ∀ i : Fin 2,
      if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
    IsFinitePLBallPair V3 (D.space ∩ cuts)
      {z | z ∈ D.space ∧ z ∈ cuts ∧
        (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)} := by
  classical
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  obtain ⟨hD, hmiss, hinside⟩ := original_interior_vertex_region_eq hAC hAR K H g hg hgPL
    M hMK reg fr arc hreg hfr harc v B hsource hface hvFr
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(v : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hvstar : (v : E) ∈ (K.closedStar v).space := by
    apply (K.closedStar v).vertices_subset_space
    change {(v : E)} ∈ K.faces ∧ insert (v : E) {(v : E)} ∈ K.faces
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (v : E)), and_self]
      using (show {(v : E)} ∈ K.faces from hvK)
  have hVB : MapsTo (fun z => (g z : X)) V.space B.source := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_space_iff.mp hz
    obtain ⟨u, hu, htu⟩ := K.exists_original_star_face_of_vertex_dual_face hvK ht
    exact hsource ((K.closedStar v).convexHull_subset_space hu (htu hzt))
  have hvA : (g v : X) ∈ A := (harc v (K.vertices_subset_space hvK)).mp
    ((M arc).vertices_subset_space v.property)
  have hvzero (i : Fin 2) : B (g v) i.castSucc = 0 := by
    have hz := ((haxis (g v) (hsource hvstar)).mp hvA).2
    fin_cases i
    · exact hz.1
    · exact hz.2
  have hcoord (z : E) (hz : z ∈ V.space) (i : Fin 2) :
      z ∈ (M (sheet i)).space ↔ B (g z) i.castSucc = 0 := by
    rw [hsheet i z (hVK hz), hsheets i (g z) (hVB hz)]
    exact and_iff_right (interior_subset (hinside z hz))
  have hball := isFinitePLBallPair_original_vertex_coordinate_sector K H g hg v hvK
    (hAC hvA) B hsource hface hvzero signs
  dsimp only at hball ⊢
  rw [hD]
  convert hball using 1
  ext z
  constructor
  · rintro ⟨hz, hc, hl | hf | ⟨i, hi⟩⟩
    · exact ⟨hz, hc, Or.inl hl⟩
    · exact (Set.disjoint_left.mp hmiss hz hf).elim
    · exact ⟨hz, hc, Or.inr ⟨i, (hcoord z hz i).mp hi⟩⟩
  · rintro ⟨hz, hc, hl | ⟨i, hi⟩⟩
    · exact ⟨hz, hc, Or.inl hl⟩
    · exact ⟨hz, hc, Or.inr (Or.inr ⟨i, (hcoord z hz i).mpr hi⟩)⟩

end PoincareConjecture.M76.Dehn
