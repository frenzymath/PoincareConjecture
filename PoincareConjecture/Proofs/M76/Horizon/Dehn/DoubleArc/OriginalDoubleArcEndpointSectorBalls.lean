import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeFaces
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalHalfBlocks









set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

open Classical in


theorem isFinitePLBallPair_original_endpoint_sector
    {E X κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {R C A : Set X} (hAC : A ⊆ interior C) (S : Fin 2 → Set X)
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space →
      (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (v : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z)))
    (haxis : ∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0)
    (hsheets : ∀ i y, y ∈ B.source →
      (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0))
    (hregion : B.source ⊆ interior R ∨
      (∀ y ∈ B.source, y ∈ R ↔ 0 ≤ B y 2) ∧
      ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0)
    (hvFr : (g v : X) ∈ frontier R) (signs : Fin 2 → Bool) :
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
  let J := K.barycentricSubdivision
  have hJs : J.space = K.space := K.barycentricSubdivision_isSubdivision.space_eq
  let H' : C ≃ₜ J.space := H.trans (Homeomorph.setCongr hJs.symm)
  have hg' (z : J.space) : (g z : X) = (H'.symm z : X) :=
    hg ⟨z, hJs.subset z.property⟩
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hvJ : (v : E) ∈ J.vertices := K.barycentricSubdivision_isSubdivision.vertices_subset hvK
  have hvA : (g v : X) ∈ A := (harc v (K.vertices_subset_space hvK)).mp
    ((M arc).vertices_subset_space v.property)
  have hVeq : V = J.closedStar v := K.barycentricDualBlock_singleton_eq_closedStar hvK
  have hVfin : V.faces.Finite := K.barycentricDualBlock_finite {(v : E)}
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(v : E)})).trans hJs.subset
  have hcontain : ∀ s ∈ V.faces, ∃ t ∈ (K.closedStar v).faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) :=
    fun _ hs => K.exists_original_star_face_of_vertex_dual_face hvK hs
  have hVstar : V.space ⊆ (K.closedStar v).space := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_space_iff.mp hz
    obtain ⟨t, ht, hst⟩ := hcontain s hs
    exact (K.closedStar v).convexHull_subset_space ht (hst hzs)
  have hvV : (v : E) ∈ V.vertices := by
    rw [hVeq]
    change {(v : E)} ∈ J.faces ∧ insert (v : E) {(v : E)} ∈ J.faces
    exact ⟨hvJ, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (v : E))]
      using (show {(v : E)} ∈ J.faces from hvJ)⟩
  have hVself : V.closedStar v = V := by
    rw [hVeq]
    ext s
    change ((s ∈ J.faces ∧ insert (v : E) s ∈ J.faces) ∧
      insert (v : E) s ∈ J.faces ∧ insert (v : E) (insert (v : E) s) ∈ J.faces) ↔
      s ∈ J.faces ∧ insert (v : E) s ∈ J.faces
    simp only [Finset.insert_idem, and_self, and_assoc]
  have hVB : MapsTo (fun z => (g z : X)) V.space B.source := fun _ hz => hsource (hVstar hz)
  have hVface : V.AffineOnFaces (fun z => B (g z)) := hface.of_face_containment hcontain
  have hnb := J.exists_original_open_neighborhood_inside_closedStar
    K.barycentricSubdivision_finite H' g hg' hvJ (hAC hvA) B (hVeq ▸ hVB)
  rw [← hVeq] at hnb
  obtain ⟨hinj, _, hint⟩ := hnb
  have hvB : (g v : X) ∈ B.source := hVB (V.vertices_subset_space hvV)
  obtain ⟨hhalf, hfront⟩ := hregion.resolve_left
    (fun h => disjoint_left.mp disjoint_interior_frontier (h hvB) hvFr)
  have hBzero : B (g v) = (0 : V3) := by
    have hz := ((haxis (g v) hvB).mp hvA).2
    ext j
    fin_cases j
    · exact hz.1
    · exact hz.2
    · exact (hfront (g v) hvB).mp hvFr
  have hD : D.space = V.space ∩ (M reg).space :=
    (K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) {(v : E)}).symm
  have hDV : D.space ⊆ V.space := hD.subset.trans inter_subset_left
  have hDR (z : E) (hz : z ∈ V.space) : z ∈ D.space ↔ (g z : X) ∈ R := by
    rw [hD]
    exact ⟨fun h => (hreg z (hVK hz)).mp h.2,
      fun h => ⟨hz, (hreg z (hVK hz)).mpr h⟩⟩
  have hDs (i : Fin 2) (z : E) (hz : z ∈ D.space) :
      z ∈ (M (sheet i)).space ↔ B (g z) i.castSucc = 0 := by
    rw [hsheet i z (hVK (hDV hz)), hsheets i (g z) (hVB (hDV hz))]
    exact and_iff_right ((hDR z (hDV hz)).mp hz)
  have hFr (z : E) (hz : z ∈ V.space) : z ∈ (M fr).space ↔ B (g z) 2 = 0 :=
    (hfr z (hVK hz)).trans (hfront (g z) (hVB hz))
  let cuts : (Fin 2 ⊕ Unit) → V3 →ₗ[ℝ] ℝ := Sum.elim
    (fun i => if signs i then LinearMap.proj i.castSucc else -(LinearMap.proj i.castSucc))
    (fun _ => LinearMap.proj 2)
  have hpositive : ∃ w : V3, ∀ j, 0 < cuts j w := by
    let w : V3 := ![if signs 0 then 1 else -1, if signs 1 then 1 else -1, 1]
    refine ⟨w, ?_⟩
    rintro (i | u)
    · fin_cases i
      · cases hs : signs 0 <;> norm_num [cuts, w, hs]
      · cases hs : signs 1 <;> norm_num [cuts, w, hs]
    · change (0 : ℝ) < 1
      exact zero_lt_one
  have hcutmem (z : E) : (∀ j, 0 ≤ cuts j (B (g z))) ↔
      0 ≤ B (g z) 2 ∧ ∀ i : Fin 2,
        if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0 := by
    constructor
    · intro h
      refine ⟨h (Sum.inr ()), ?_⟩
      intro i
      cases hs : signs i <;> simpa [cuts, hs] using h (Sum.inl i)
    · rintro ⟨h2, hi⟩ (i | u)
      · cases hs : signs i <;> simpa [cuts, hs] using hi i
      · exact h2
  have hcutzero (z : E) : (∃ j, cuts j (B (g z)) = 0) ↔
      B (g z) 2 = 0 ∨ ∃ i : Fin 2, B (g z) i.castSucc = 0 := by
    have hi (i : Fin 2) : cuts (Sum.inl i) (B (g z)) = 0 ↔ B (g z) i.castSucc = 0 := by
      cases hs : signs i <;> simp [cuts, hs]
    simp only [Sum.exists, hi, cuts, Sum.elim_inr, LinearMap.proj_apply, exists_const, or_comm]
  have hbody : V.space ∩ {z | ∀ j, 0 ≤ cuts j (B (g z))} =
      D.space ∩ {z | ∀ i : Fin 2,
        if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0} := by
    ext z
    constructor
    · rintro ⟨hz, hc⟩
      exact ⟨(hDR z hz).mpr ((hhalf (g z) (hVB hz)).mpr ((hcutmem z).mp hc).1),
        ((hcutmem z).mp hc).2⟩
    · rintro ⟨hz, hc⟩
      exact ⟨hDV hz, (hcutmem z).mpr
        ⟨(hhalf (g z) (hVB (hDV hz))).mp ((hDR z (hDV hz)).mp hz), hc⟩⟩
  have hrim : {z | z ∈ V.space ∧ (∀ j, 0 ≤ cuts j (B (g z))) ∧
      (z ∈ (V.link v).space ∨ ∃ j, cuts j (B (g z)) = 0)} =
      {z | z ∈ D.space ∧ (∀ i : Fin 2,
        if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0) ∧
        (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)} := by
    ext z
    constructor
    · rintro ⟨hz, hc, hr⟩
      have hd := hbody.subset ⟨hz, hc⟩
      refine ⟨hd.1, hd.2, ?_⟩
      rcases hr with hl | hh
      · exact Or.inl hl
      · rcases (hcutzero z).mp hh with hf | ⟨i, hi⟩
        · exact Or.inr (Or.inl ((hFr z hz).mpr hf))
        · exact Or.inr (Or.inr ⟨i, (hDs i z hd.1).mpr hi⟩)
    · rintro ⟨hz, hc, hr⟩
      have hv := hbody.superset ⟨hz, hc⟩
      refine ⟨hv.1, hv.2, ?_⟩
      rcases hr with hl | hf | ⟨i, hi⟩
      · exact Or.inl hl
      · exact Or.inr ((hcutzero z).mpr (Or.inl ((hFr z hv.1).mp hf)))
      · exact Or.inr ((hcutzero z).mpr (Or.inr ⟨i, (hDs i z hz).mp hi⟩))
  have hball := hVface.isFinitePLBallPair_conical_halfspaces hVfin hinj hvV hVself
    hBzero (hBzero ▸ hint) (ContinuousLinearEquiv.refl ℝ V3) cuts hpositive
  simpa only [hbody, hrim, mem_setOf_eq] using hball

end PoincareConjecture.M76.Dehn
