import PoincareConjecture.Proofs.M76.Dehn.OriginalChartConnectedLinks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspaceContractibleLinks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineLinkHomeomorph

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

theorem contractibleSpace_faceLink_of_original_boundary_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ K.vertices) (hpfront : (g p : X) ∈ frontier R)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ContractibleSpace (K.faceLink {p}).space := by
  classical
  let a : E → V3 := fun z => B (g z)
  let S := K.closedStar p
  have hpface : {p} ∈ K.faces := K.mem_vertices.mp hp
  have hsS : {p} ∈ S.faces := ⟨hpface, by simpa using hpface⟩
  have hpS : p ∈ S.space := S.subset_space hsS (Finset.mem_singleton_self p)
  rcases hregion with hinterior | ⟨ell, v, hv, hhalf⟩
  · exact False.elim (hpfront.2
      (interior_maximal hinterior B.open_source (hsource hpS)))
  obtain ⟨hinj, O, hO, hpO, hOB, hOR⟩ :=
    K.exists_original_open_neighborhood_of_closedStar hK H g hg hp B hsource
  let J := hface.embeddedImage hinj
  have hS : S.faces.Finite := hK.subset (fun _ ht => ht.1)
  have hJ : J.faces.Finite := hface.embeddedImage_finite hinj hS
  have hpJ : a p ∈ J.vertices := by
    apply J.mem_vertices.mpr
    have hsJ := (hface.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
    simpa only [Finset.image_singleton] using hsJ
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    exact zero_ne_one hval
  have hfront := B.isImage_frontier_of_affine_nonneg ell hell hhalf
  have hzero : ell (a p) = 0 :=
    (hfront.apply_mem_iff (hsource hpS)).mpr hpfront
  have hcontract : ContractibleSpace (J.faceLink {a p}).space := by
    apply J.contractibleSpace_faceLink_singleton_of_halfspace_patch hJ hpJ ell hell hzero
      (V := B '' O)
    · rw [hface.embeddedImage_space hinj]
      rintro _ ⟨z, hz, rfl⟩
      exact (hhalf (g z) (hsource hz)).mp (g z).property
    · exact B.isOpen_image_of_subset_source hO hOB
    · exact mem_image_of_mem B hpO
    · rw [hface.embeddedImage_space hinj]
      rintro z ⟨⟨x, hxO, rfl⟩, hxell⟩
      obtain ⟨y, hy, hyx⟩ := hOR ⟨hxO, (hhalf x (hOB hxO)).mpr hxell⟩
      exact ⟨y, hy, congrArg B hyx⟩
  let : ContractibleSpace (J.faceLink (({p} : Finset E).image a)).space := by
    rw [Finset.image_singleton]
    exact hcontract
  have hsourceLink :=
    (hface.faceLinkHomeomorphEmbeddedImage hinj hS hsS).contractibleSpace
  have hSl : S.faceLink {p} = K.faceLink {p} := by
    change (K.closedStar p).faceLink {p} = K.faceLink {p}
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.Subset.refl _)
  rwa [hSl] at hsourceLink

end PoincareConjecture.M76
