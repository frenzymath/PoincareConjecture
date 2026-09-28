import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubpolyhedronZeroSet
import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh

theorem exists_affine_full_subcomplex_zero_height
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (K M : SimplicialComplex ℝ D) (hMK : M ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ M.vertices) → s ∈ M.faces) :
    ∃ f : D → ℝ, K.AffineOnFaces f ∧
      ∀ x ∈ K.space, 0 ≤ f x ∧ (f x = 0 ↔ x ∈ M.space) := by
  classical
  obtain ⟨f, hf, hfv⟩ := K.exists_affineOnFaces_eqOn_vertices
    (fun x => if x ∈ M.vertices then (0 : ℝ) else 1)
  have hfM : M.AffineOnFaces f := fun s hs => hf s (hMK hs)
  have hzeroM : EqOn f (fun _ => 0) M.space := by
    apply hfM.eqOn_of_eqOn_vertices
      (M.affineOnFaces_affine (ContinuousAffineMap.const ℝ D (0 : ℝ)))
    intro v hv
    change f v = 0
    simpa only [if_pos hv] using hfv (hMK hv)
  refine ⟨f, hf, fun x hx => ?_⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hf s hs
  have hav (v : D) (hv : v ∈ s) : a v = if v ∈ M.vertices then 0 else 1 :=
    (ha (subset_convexHull ℝ _ hv)).symm.trans
      (hfv (K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)))
  have hnonneg (v : D) (hv : v ∈ s) : 0 ≤ a v := by
    rw [hav v hv]
    split_ifs <;> norm_num
  have hxnonneg : 0 ≤ a x :=
    convexHull_min (fun v hv => hnonneg v hv)
      (Convex.affine_preimage a.toAffineMap (convex_Ici 0)) hxs
  refine ⟨ha hxs ▸ hxnonneg, ?_⟩
  constructor
  · intro hxzero
    have hz := s.mem_convexHull_zero_vertices a.toAffineMap hnonneg hxs
      ((ha hxs).symm.trans hxzero)
    let t := s.filter (fun v => v ∈ M.vertices)
    have ht : (t : Set D) = (s : Set D) ∩ {v | a v = 0} := by
      ext v
      simp only [t, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hv, hvM⟩
        exact ⟨hv, by rw [hav v hv, if_pos hvM]⟩
      · rintro ⟨hv, hz⟩
        refine ⟨hv, ?_⟩
        by_contra hn
        rw [hav v hv, if_neg hn] at hz
        exact one_ne_zero hz
    have hxt : x ∈ convexHull ℝ (t : Set D) := ht.symm ▸ hz
    have htne := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
    have htK := K.down_closed hs (Finset.filter_subset _ _) htne
    exact M.convexHull_subset_space
      (hfull t htK (fun v hv => (Finset.mem_filter.mp hv).2)) hxt
  · exact fun hxM => hzeroM hxM

theorem vertexSubcomplex_space_of_nonnegative_affine_height
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (K : SimplicialComplex ℝ D) {f : D → ℝ}
    (hf : K.AffineOnFaces f) (hpos : ∀ x ∈ K.space, 0 ≤ f x) :
    (K.vertexSubcomplex {x | f x = 0}).space = K.space ∩ {x | f x = 0} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := hf s hs.1
    refine ⟨K.convexHull_subset_space hs.1 hxs, ?_⟩
    have heq : EqOn a.toAffineMap (AffineMap.const ℝ D 0) (s : Set D) := by
      intro v hv
      exact (ha (subset_convexHull ℝ _ hv)).symm.trans (hs.2 v hv)
    exact (ha hxs).trans
      ((AffineMap.eqOn_affineSpan heq) (convexHull_subset_affineSpan _ hxs))
  · rintro ⟨hx, hxzero⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := hf s hs
    have hav (v : D) (hv : v ∈ s) : f v = a v := ha (subset_convexHull ℝ _ hv)
    have hz := s.mem_convexHull_zero_vertices a.toAffineMap
      (fun v hv => (hav v hv) ▸ hpos v
        (K.convexHull_subset_space hs (subset_convexHull ℝ _ hv)))
      hxs ((ha hxs).symm.trans hxzero)
    let t := s.filter (fun v => f v = 0)
    have ht : (t : Set D) = (s : Set D) ∩ {v | a v = 0} := by
      ext v
      simp only [t, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_ofPred_eq]
      exact and_congr_right (fun hv => by rw [hav v hv])
    have hxt : x ∈ convexHull ℝ (t : Set D) := ht.symm ▸ hz
    have htne := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
    exact SimplicialComplex.mem_space_iff.mpr ⟨t,
      ⟨K.down_closed hs (Finset.filter_subset _ _) htne,
        fun v hv => (Finset.mem_filter.mp hv).2⟩, hxt⟩

theorem exists_full_subcomplex_of_subdivision
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (K M N : SimplicialComplex ℝ D) (hMK : M ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ M.vertices) → s ∈ M.faces)
    (hN : N.faces.Finite) (hNK : N.IsSubdivision K) :
    ∃ L : SimplicialComplex ℝ D, L ≤ N ∧ L.faces.Finite ∧ L.space = M.space ∧
      ∀ s ∈ N.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces := by
  obtain ⟨f, hf, hzero⟩ := exists_affine_full_subcomplex_zero_height K M hMK hfull
  let L := N.vertexSubcomplex {x | f x = 0}
  have hLs : L.space = N.space ∩ {x | f x = 0} :=
    vertexSubcomplex_space_of_nonnegative_affine_height N (hNK.affineOnFaces hf)
      (fun x hx => (hzero x (hNK.space_eq.subset hx)).1)
  refine ⟨L, N.vertexSubcomplex_le _, N.vertexSubcomplex_finite _ hN, ?_, ?_⟩
  · rw [hLs]
    ext x
    constructor
    · exact fun hx => (hzero x (hNK.space_eq.subset hx.1)).2.mp hx.2
    · intro hx
      have hxK : x ∈ K.space := by
        obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
        exact K.convexHull_subset_space (hMK hs) hxs
      exact ⟨hNK.space_eq.symm.subset hxK, (hzero x hxK).2.mpr hx⟩
  · intro s hs hverts
    refine ⟨hs, fun v hv => ?_⟩
    have hvL := hverts v hv
    rw [N.vertexSubcomplex_vertices] at hvL
    exact hvL.2

end PoincareConjecture.M76.CollarMesh
