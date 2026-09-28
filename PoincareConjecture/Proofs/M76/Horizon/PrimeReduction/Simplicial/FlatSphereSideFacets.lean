import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

private theorem faceLink_one_of_halfspace_chart
    (P : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ P.faces) (hsc : s.card = 3)
    {p : E} (hps : p ∈ s) {f : E → (Fin 3 → ℝ)}
    (hf : (P.closedStar p).AffineOnFaces f) (hinj : InjOn f (P.closedStar p).space)
    (ell : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (v : Fin 3 → ℝ) (hv : ell.contLinear v = 1)
    (hhalf : ∀ x ∈ (P.closedStar p).space, 0 ≤ ell (f x))
    (hzero : ∀ x ∈ s, ell (f x) = 0)
    (hne : (P.faceLink s).vertices.Nonempty) :
    (P.faceLink s).vertices.ncard = 1 := by
  classical
  let S := P.closedStar p
  have hsS : s ∈ S.faces := ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  obtain ⟨q, hq⟩ := hne
  have hqs : q ∉ s := (P.faceLink_vertices_subset s hq).2
  have ht : insert q s ∈ P.faces := by
    simpa only [Finset.union_singleton] using hq.2.2
  have htS : insert q s ∈ S.faces := ⟨ht, by
    simpa only [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hps)] using ht⟩
  let J := hf.embeddedImage hinj
  have hsJ : s.image f ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  have htJ : (insert q s).image f ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hinj (S.subset_space htS)).mpr htS
  have hscJ : (s.image f).card = Module.finrank ℝ (Fin 3 → ℝ) := by
    rw [Finset.card_image_iff.mpr (hinj.mono (S.subset_space hsS)), hsc]
    simp
  have htcJ : ((insert q s).image f).card = Module.finrank ℝ (Fin 3 → ℝ) + 1 := by
    rw [Finset.card_image_iff.mpr (hinj.mono (S.subset_space htS)),
      Finset.card_insert_of_notMem hqs, hsc]
    simp
  have hJhalf : J.space ⊆ {x | 0 ≤ ell x} := by
    rw [hf.embeddedImage_space hinj]
    rintro x ⟨y, hy, rfl⟩
    exact hhalf y hy
  have hJzero : ∀ x ∈ convexHull ℝ (s.image f : Set (Fin 3 → ℝ)), ell x = 0 := by
    have hverts : EqOn ell.toAffineMap (AffineMap.const ℝ (Fin 3 → ℝ) 0)
        (s.image f : Set (Fin 3 → ℝ)) := by
      rintro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hzero y hy
    exact fun x hx => AffineMap.eqOn_affineSpan hverts (convexHull_subset_affineSpan _ hx)
  have hc := J.faceLink_ncard_eq_one_of_halfspace hsJ hscJ htJ
    (Finset.image_subset_image (Finset.subset_insert q s)) htcJ ell v hv hJhalf hJzero
  rw [hf.ncard_embeddedImage_faceLink hinj hsS] at hc
  have hSl : S.faceLink s = P.faceLink s := by
    change (P.closedStar p).faceLink s = P.faceLink s
    rw [← P.closedFaceStar_singleton_eq_closedStar]
    exact P.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hSl] at hc

theorem faceLink_ncard_eq_one_each_side_of_flat_chart
    (K N P M : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hPK : P ≤ K) (hMK : M ≤ K) (hNP : N ≤ P) (hNM : N ≤ M)
    {s : Finset E} (hs : s ∈ N.faces) (hsc : s.card = 3)
    {p : E} (hps : p ∈ s) {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hP : (P.closedStar p).space = (K.closedStar p).space ∩ {x | 0 ≤ f x 0})
    (hM : (M.closedStar p).space = (K.closedStar p).space ∩ {x | f x 0 ≤ 0})
    (hN : (N.closedStar p).space = (K.closedStar p).space ∩ {x | f x 0 = 0})
    (hcover : ∀ t ∈ (K.closedStar p).faces, t ∈ P.faces ∨ t ∈ M.faces) :
    (P.faceLink s).vertices.ncard = 1 ∧ (M.faceLink s).vertices.ncard = 1 := by
  classical
  have hsK := hPK (hNP hs)
  have hsstar : s ∈ (K.closedStar p).faces :=
    ⟨hsK, by simpa only [Finset.insert_eq_of_mem hps] using hsK⟩
  have hsNstar : s ∈ (N.closedStar p).faces :=
    ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  have hzero (x : E) (hx : x ∈ s) : f x 0 = 0 :=
    (hN.subset ((N.closedStar p).subset_space hsNstar hx)).2
  let J := hf.embeddedImage hinj
  have hJ := hf.embeddedImage_finite hinj (finite_closedStar_faces hK p)
  have hsJ : s.image f ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hinj ((K.closedStar p).subset_space hsstar)).mpr hsstar
  have hscJ : (s.image f).card = Module.finrank ℝ (Fin 3 → ℝ) := by
    rw [Finset.card_image_iff.mpr (hinj.mono ((K.closedStar p).subset_space hsstar)), hsc]
    simp
  have hintJ : f p ∈ interior J.space := by
    rw [hf.embeddedImage_space hinj]
    exact hint
  have hcount := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hscJ
    ⟨f p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  rw [hf.ncard_embeddedImage_faceLink hinj hsstar] at hcount
  have hSl : (K.closedStar p).faceLink s = K.faceLink s := by
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rw [hSl] at hcount
  have hPstarle : P.closedStar p ≤ K.closedStar p := fun _ ht => ⟨hPK ht.1, hPK ht.2⟩
  have hMstarle : M.closedStar p ≤ K.closedStar p := fun _ ht => ⟨hMK ht.1, hMK ht.2⟩
  let ell : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 3) (R := ℝ) (φ := fun _ => ℝ)).toContinuousAffineMap
  have hPone (hne : (P.faceLink s).vertices.Nonempty) : (P.faceLink s).vertices.ncard = 1 := by
    apply faceLink_one_of_halfspace_chart P (hNP hs) hsc hps
      (fun t ht => hf t (hPstarle ht))
      (hinj.mono (space_subset_of_le hPstarle)) ell (fun _ => 1) rfl
      (fun x hx => (hP.subset hx).2) hzero hne
  have hMone (hne : (M.faceLink s).vertices.Nonempty) : (M.faceLink s).vertices.ncard = 1 := by
    apply faceLink_one_of_halfspace_chart M (hNM hs) hsc hps
      (fun t ht => hf t (hMstarle ht))
      (hinj.mono (space_subset_of_le hMstarle)) (-ell) (fun _ => -1) (by norm_num [ell])
      (fun x hx => neg_nonneg.mpr (hM.subset hx).2) (fun x hx => by
        change -(f x 0) = 0
        rw [hzero x hx, neg_zero]) hne
  have hunion : (K.faceLink s).vertices = (P.faceLink s).vertices ∪ (M.faceLink s).vertices := by
    ext x
    constructor
    · intro hx
      have ht : s ∪ {x} ∈ (K.closedStar p).faces := ⟨hx.2.2, by
        simpa only [Finset.insert_eq_of_mem (Finset.mem_union_left _ hps)] using hx.2.2⟩
      rcases hcover _ ht with htP | htM
      · left
        exact ⟨P.down_closed htP Finset.subset_union_right (Finset.singleton_nonempty x), hx.2.1, htP⟩
      · right
        exact ⟨M.down_closed htM Finset.subset_union_right (Finset.singleton_nonempty x), hx.2.1, htM⟩
    · rintro (hx | hx)
      · exact ⟨hPK hx.1, hx.2.1, hPK hx.2.2⟩
      · exact ⟨hMK hx.1, hx.2.1, hMK hx.2.2⟩
  have hPne : (P.faceLink s).vertices.Nonempty := by
    by_contra h
    have hempty := Set.not_nonempty_iff_eq_empty.mp h
    rw [hempty, empty_union] at hunion
    have hMne : (M.faceLink s).vertices.Nonempty := by
      rw [← hunion]
      exact Set.nonempty_of_ncard_ne_zero (by omega)
    have hone := hMone hMne
    rw [← hunion] at hone
    omega
  have hMne : (M.faceLink s).vertices.Nonempty := by
    by_contra h
    have hempty := Set.not_nonempty_iff_eq_empty.mp h
    rw [hempty, union_empty] at hunion
    have hone := hPone hPne
    rw [← hunion] at hone
    omega
  exact ⟨hPone hPne, hMone hMne⟩

end Geometry.SimplicialComplex
