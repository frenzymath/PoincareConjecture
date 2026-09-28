import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcJointStrictPoints
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.StrictCoordinateFrontierPatch










set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem exists_original_interior_sector_exterior_point
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (v : (M arc).vertices) (hvFr : (g v : X) ∉ frontier R)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ (M arc).faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, (v : E) ∈ s j)
    (hdisj : Disjoint (K.barycentricDualBlock (s false)).space
      (K.barycentricDualBlock (s true)).space)
    (C0 : Set V3) (theta : (K.barycentricDualBlock {(v : E)}).space ≃ₜ C0)
    (hC : IsCompact C0) (hcv : Convex ℝ C0) (hzero : (0 : V3) ∈ interior C0)
    (hlink : ∀ z : (K.barycentricDualBlock {(v : E)}).space,
      (z : E) ∈ ((K.barycentricDualBlock {(v : E)}).link v).space ↔
        (theta z : V3) ∈ frontier C0)
    (hmarks : ∀ i : Fin 2, ∀ z : (K.barycentricDualBlock {(v : E)}).space,
      ((theta z : V3) i.castSucc = 0 ↔ B v (g z) i.castSucc = 0) ∧
      (0 ≤ (theta z : V3) i.castSucc ↔ 0 ≤ B v (g z) i.castSucc))
    (signs : Fin 2 → Bool) :
    ∃ z ∈ ((M reg).barycentricDualBlock {(v : E)}).space,
      z ∈ ((K.barycentricDualBlock {(v : E)}).link v).space ∧
      (∀ j, z ∉ (K.barycentricDualBlock (s j)).space) ∧
      z ∉ (M fr).space ∧ (∀ i, z ∉ (M (sheet i)).space) ∧
      ∀ i : Fin 2, if signs i then 0 < B v (g z) i.castSucc
        else B v (g z) i.castSucc < 0 := by
  classical
  let V := K.barycentricDualBlock {(v : E)}
  let J := fun j => (K.barycentricDualBlock (s j)).space
  have hJV (j : Bool) : J j ⊆ V.space :=
    space_subset_of_le (K.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr (hvs j)))
  have hJ (j : Bool) : IsCompact (J j) :=
    (K.barycentricDualBlock (s j)).isCompact_space_of_finite (K.barycentricDualBlock_finite (s j))
  have hm (j : Bool) : ∃ z : V.space, (z : E) ∈ J j ∧
      (theta z : V3) ∈ frontier C0 ∧ (theta z : V3) ∈ strictCoordinateWedge signs := by
    obtain ⟨z, hzJ, hzlink, hzstrict⟩ := exists_original_joint_strict_point
      hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB (s j) (hs j) (hcard j) v (hvs j) signs
    let zv : V.space := ⟨z, hJV j hzJ⟩
    refine ⟨zv, hzJ, (hlink zv).mp hzlink, ?_⟩
    intro i
    have hi := hzstrict i
    cases hiSign : signs i <;> simp only [hiSign, Bool.false_eq_true, ↓reduceIte] at hi ⊢
    · exact lt_of_not_ge (fun h => not_le_of_gt hi ((hmarks i zv).2.mp h))
    · refine lt_of_le_of_ne ((hmarks i zv).2.mpr hi.le) ?_
      intro hz
      exact hi.ne' ((hmarks i zv).1.mp hz.symm)
  obtain ⟨z, hzfront, hzstrict, hzJ⟩ :=
    exists_strict_chart_frontier_point_outside_two_compact_sets theta hC hcv hzero
      J hJ hJV hdisj signs hm
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(v : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hvstar : (v : E) ∈ (K.closedStar v).space := by
    apply (K.closedStar v).vertices_subset_space
    change {(v : E)} ∈ K.faces ∧ insert (v : E) {(v : E)} ∈ K.faces
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (v : E)), and_self]
      using (show {(v : E)} ∈ K.faces from hvK)
  have hVsource : MapsTo (fun x => (g x : X)) V.space (B v).source := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨u, hu, htu⟩ := K.exists_original_star_face_of_vertex_dual_face hvK ht
    exact (hB v).1 ((K.closedStar v).convexHull_subset_space hu (htu hxt))
  have hvnot : (v : E) ∉ (M fr).vertices := fun h => hvFr
    ((hfr v (K.vertices_subset_space hvK)).mp ((M fr).vertices_subset_space h))
  have hfoot : V.space ∩ (M fr).space = ∅ := by
    rw [K.barycentricDualBlock_space_inter_subcomplex (M fr) (hMK fr) {(v : E)}]
    exact (M fr).barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.singleton_nonempty (v : E)) hvnot
  have hVconn : IsConnected V.space := by
    apply isConnected_iff_connectedSpace.mpr
    exact theta.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp
      (hcv.isConnected ⟨0, interior_subset hzero⟩))
  have hconn := hVconn.isPreconnected.image (fun x => (g x : X))
    (hgPL.continuousOn.mono hVK)
  have havoid : Disjoint (frontier (interior R)) ((fun x => (g x : X)) '' V.space) := by
    apply Set.disjoint_left.mpr
    rintro _ hx ⟨w, hw, rfl⟩
    exact (hfoot.subset ⟨hw, (hfr w (hVK hw)).mpr (frontier_interior_subset hx)⟩).elim
  have hvA : (g v : X) ∈ A := (harc v (K.vertices_subset_space hvK)).mp
    ((M arc).vertices_subset_space v.property)
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
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (v : E)), and_self]
      using hvJs
  have hzR : (g z : X) ∈ interior R :=
    hconn.m76_subset_of_disjoint_frontier isOpen_interior havoid
      ⟨g v, mem_image_of_mem _ hvV, hvR⟩ (mem_image_of_mem _ z.property)
  have hzD : (z : E) ∈ ((M reg).barycentricDualBlock {(v : E)}).space := by
    rw [← K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) {(v : E)}]
    exact ⟨z.property, (hreg z (hVK z.property)).mpr (interior_subset hzR)⟩
  have hstrict (i : Fin 2) :
      if signs i then 0 < B v (g z) i.castSucc else B v (g z) i.castSucc < 0 := by
    have hi := hzstrict i
    cases hiSign : signs i <;> simp only [hiSign, Bool.false_eq_true, ↓reduceIte] at hi ⊢
    · exact lt_of_not_ge (fun h => not_le_of_gt hi ((hmarks i z).2.mpr h))
    · refine lt_of_le_of_ne ((hmarks i z).2.mp hi.le) ?_
      intro hz
      exact hi.ne' ((hmarks i z).1.mpr hz.symm)
  refine ⟨z, hzD, (hlink z).mpr hzfront, hzJ, ?_, ?_, hstrict⟩
  · intro hz
    exact (hfoot.subset ⟨z.property, hz⟩).elim
  · intro i hz
    have heq := ((hB v).2.2.2 i (g z) (hVsource z.property)).mp
      ((hsheet i z (hVK z.property)).mp hz)
    have hi := hstrict i
    cases hiSign : signs i <;> simp only [hiSign, Bool.false_eq_true, ↓reduceIte, heq.2] at hi <;>
      exact lt_irrefl 0 hi

end PoincareConjecture.M76.Dehn
