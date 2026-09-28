import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.OriginalContactGraph
import PoincareConjecture.Proofs.M76.PrimeReduction.AffineContactFiniteness
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds












set_option autoImplicit false

open Set Geometry Module

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem graph_image_finite_line_cover
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hbound : ∀ a ∈ J.faces, a.card ≤ 2) {f : V3 → V3}
    (hf : J.AffineOnFaces f) :
    ∃ Q : Finset (AffineSubspace ℝ V3),
      (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
      ∀ x ∈ f '' J.space, ∃ L ∈ Q, x ∈ L := by
  classical
  let line (a : Finset V3) := affineSpan ℝ (a.image f : Set V3)
  refine ⟨hJ.toFinset.image line, ?_, ?_⟩
  · intro L hL
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hL
    have haJ := hJ.mem_toFinset.mp ha
    exact finrank_affineSpan_finset_le ((J.nonempty_of_mem_faces haJ).image f)
      (Finset.card_image_le.trans (hbound a haJ))
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hya⟩ := SimplicialComplex.mem_space_iff.mp hy
    refine ⟨line a, Finset.mem_image.mpr ⟨a, hJ.mem_toFinset.mpr ha, rfl⟩, ?_⟩
    apply convexHull_subset_affineSpan (s := (a.image f : Set V3))
    rw [Finset.coe_image, ← hf.image_convexHull ha]
    exact mem_image_of_mem f hya

private theorem contact_graph_line_cover_in_chart
    {X : Type*} [TopologicalSpace X]
    (I B Q : OpenPartialHomeomorph X V3)
    (hB : I.symm.trans B ∈ piecewiseAffineGroupoid V3)
    (hQ : I.symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {y : X} (hyI : y ∈ I.source) (hyB : y ∈ B.source) (hyQ : y ∈ Q.source)
    (D : Set X) (N : Set V3) (hyN : B y ∈ interior N)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJs : J.space = (B '' (D ∩ B.source)) ∩ N)
    (hbound : ∀ a ∈ J.faces, a.card ≤ 2) :
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      (∀ A ∈ L, finrank ℝ A.direction ≤ 1) ∧
      ∀ x ∈ (Q '' (D ∩ Q.source)) ∩ U, ∃ A ∈ L, x ∈ A := by
  classical
  let C := (I.symm.trans B).symm.trans (I.symm.trans Q)
  have hC : C ∈ piecewiseAffineGroupoid V3 :=
    (piecewiseAffineGroupoid V3).trans ((piecewiseAffineGroupoid V3).symm hB) hQ
  have hyC : B y ∈ C.source := by
    change (B y ∈ B.target ∧ B.symm (B y) ∈ I.source) ∧
      (I (B.symm (B y)) ∈ I.target ∧ I.symm (I (B.symm (B y))) ∈ Q.source)
    simpa only [B.left_inv hyB, I.left_inv hyI] using
      And.intro (And.intro (B.map_source hyB) hyI) (And.intro (I.map_source hyI) hyQ)
  have hCy : C (B y) = Q y := by
    change Q (I.symm (I (B.symm (B y)))) = Q y
    rw [B.left_inv hyB, I.left_inv hyI]
  have hCsymm (x : V3) (hx : x ∈ C.target) : C.symm x = B (Q.symm x) := by
    change B (I.symm (I (Q.symm x))) = B (Q.symm x)
    rw [I.left_inv hx.1.2]
  obtain ⟨R, hR, hyR, _, hfR⟩ :=
    ((mem_piecewiseAffineGroupoid_iff V3 C).mp hC).1 (B y) hyC
  obtain ⟨K, hK, hKs⟩ := J.exists_finite_triangulation_inter R hJ hR
  have hfK : FinitePiecewiseAffineOn C K.space :=
    (hfR.finitePiecewiseAffineOn hR).restrict K hK (hKs.subset.trans inter_subset_right)
  obtain ⟨M, hM, hMs, hfM⟩ := hfK
  have hMbound (a : Finset V3) (ha : a ∈ M.faces) : a.card ≤ 2 :=
    M.face_card_le_of_hull_subset_finite_carrier J hJ ha
      ((M.convexHull_subset_space ha).trans
        (hMs.subset.trans (hKs.subset.trans inter_subset_left))) hbound
  obtain ⟨L, hL, hcover⟩ := graph_image_finite_line_cover M hM hMbound hfM
  let U := C.target ∩ C.symm ⁻¹' (interior N ∩ interior R.space)
  have hU : IsOpen U := C.symm.isOpen_inter_preimage (isOpen_interior.inter isOpen_interior)
  have hyU : Q y ∈ U := by
    have htarget : Q y ∈ C.target := hCy ▸ C.map_source hyC
    refine ⟨htarget, ?_⟩
    change C.symm (Q y) ∈ interior N ∩ interior R.space
    rw [← hCy, C.left_inv hyC]
    exact ⟨hyN, hyR⟩
  refine ⟨U, L, hU, hyU, fun _ hx => hx.1.1.1, hL, ?_⟩
  rintro x ⟨⟨z, ⟨hzD, hzQ⟩, rfl⟩, hxU⟩
  have hzI : z ∈ I.source := by
    have hh := hxU.1.1.2
    change Q.symm (Q z) ∈ I.source at hh
    rwa [Q.left_inv hzQ] at hh
  have hzB : z ∈ B.source := by
    have hh := hxU.1.2.2
    change I.symm (I (Q.symm (Q z))) ∈ B.source at hh
    rwa [Q.left_inv hzQ, I.left_inv hzI] at hh
  have hback : C.symm (Q z) = B z := by rw [hCsymm _ hxU.1, Q.left_inv hzQ]
  apply hcover (Q z)
  refine ⟨C.symm (Q z), hMs.symm.subset (hKs.symm.subset ?_), C.right_inv hxU.1⟩
  exact ⟨hJs.symm.subset ⟨⟨z, ⟨hzD, hzB⟩, hback.symm⟩,
    interior_subset hxU.2.1⟩, interior_subset hxU.2.2⟩





theorem HasOriginalEdgeCofaceCharts.exists_surface_contact_line_cover_in_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hcover : ∀ y ∈ S, ∃ i, y ∈ (e i).source)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hyQ : y ∈ Q.source) :
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      (∀ A ∈ L, finrank ℝ A.direction ≤ 1) ∧
      ∀ x ∈ (Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source)) ∩ U,
        ∃ A ∈ L, x ∈ A := by
  obtain ⟨B, z, r, N, J, hB, hyB, _, _, _, _, _, _, _, _, hyN, _, hJ, _, hJs, _, hJc⟩ :=
    h.exists_triangle_contact_graph hgi hSV hpq hwp hwq ht hy
  obtain ⟨i, hye⟩ := hcover y hy.1
  exact contact_graph_line_cover_in_chart (e i) B Q (hB i) (hQ i)
    hye hyB hyQ (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E))) N.space hyN J hJ hJs hJc




theorem HasOriginalEdgeCofaceCharts.exists_surface_contact_line_cover_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hcover : ∀ y ∈ S, ∃ i, y ∈ (e i).source)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ ({w, p, q} : Set E))) :
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      (∀ B ∈ L, finrank ℝ B.direction ≤ 1) ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩
        convexHull ℝ (A '' ({w, p, q} : Set E))) ∩ U, ∃ B ∈ L, x ∈ B := by
  have hseg : segment ℝ p q ⊆ convexHull ℝ ({w, p, q} : Set E) := by
    rw [← convexHull_pair]
    exact convexHull_mono (by intro x hx; exact Or.inr hx)
  have hyQ : y ∈ Q.source := by
    obtain ⟨x, hx, rfl⟩ := hy.2
    exact hmap (hseg hx)
  obtain ⟨U, L, hU, hyU, hUQ, hL, hcover⟩ :=
    h.exists_surface_contact_line_cover_in_chart hcover hgi hSV hpq hwp hwq ht hy Q hQ hyQ
  have himage : convexHull ℝ (A '' ({w, p, q} : Set E)) =
      (Q ∘ g) '' convexHull ℝ ({w, p, q} : Set E) :=
    (A.toAffineMap.image_convexHull _).symm.trans (image_congr hA).symm
  refine ⟨U, L, hU, hyU, hUQ, hL, ?_⟩
  rintro x ⟨⟨⟨z, ⟨hzS, hzQ⟩, hzx⟩, hxt⟩, hxU⟩
  obtain ⟨u, hu, hux⟩ := himage.subset hxt
  have huz : g u = z := Q.injOn (hmap hu) hzQ (hux.trans hzx.symm)
  exact hcover x ⟨⟨z, ⟨⟨hzS, u, hu, huz⟩, hzQ⟩, hzx⟩, hxU⟩

end PoincareConjecture.M76

