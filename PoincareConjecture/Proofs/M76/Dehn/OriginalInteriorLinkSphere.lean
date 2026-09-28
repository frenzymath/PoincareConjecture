import PoincareConjecture.Proofs.M76.Dehn.OriginalChartConnectedLinks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.InteriorSphereLinks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineLinkHomeomorph










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]




theorem exists_faceLink_sphere_homeomorph_of_original_interior_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ K.vertices) (hpfront : (g p : X) ∉ frontier R)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    Nonempty ((K.faceLink {p}).space ≃ₜ Metric.sphere (0 : V3) 1) := by
  classical
  let a : E → V3 := fun z => B (g z)
  let S := K.closedStar p
  have hpface : {p} ∈ K.faces := K.mem_vertices.mp hp
  have hsS : {p} ∈ S.faces := ⟨hpface, by simpa using hpface⟩
  have hpS : p ∈ S.space := S.subset_space hsS (Finset.mem_singleton_self p)
  obtain ⟨hinj, V, hV, hpV, hcase⟩ :=
    exists_original_closedStar_image_neighborhood K hK H g hg hp B hsource hregion
  have hint : a p ∈ interior (a '' S.space) := by
    rcases hcase with hinside | ⟨ell, v, hv, hpatch, hhalf, hfront⟩
    · exact interior_maximal hinside hV hpV
    · have hnonneg : 0 ≤ ell (a p) := hhalf (mem_image_of_mem a hpS)
      have hne : ell (a p) ≠ 0 := fun h => hpfront ((hfront p hpS).mpr h)
      have hpos : 0 < ell (a p) := lt_of_le_of_ne hnonneg (Ne.symm hne)
      exact interior_maximal
        (fun z hz => hpatch ⟨hz.1, (show 0 < ell z from hz.2).le⟩)
        (hV.inter (isOpen_lt continuous_const ell.continuous)) ⟨hpV, hpos⟩
  let J := hface.embeddedImage hinj
  have hS : S.faces.Finite := hK.subset (fun _ ht => ht.1)
  have hJ : J.faces.Finite := hface.embeddedImage_finite hinj hS
  have hpJ : a p ∈ J.vertices := by
    apply J.mem_vertices.mpr
    have hsJ := (hface.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
    simpa only [Finset.image_singleton] using hsJ
  have hintJ : a p ∈ interior J.space := by
    rw [hface.embeddedImage_space hinj]
    exact hint
  have hmodelJ : Nonempty
      ((J.faceLink (({p} : Finset E).image a)).space ≃ₜ Metric.sphere (0 : V3) 1) := by
    rw [Finset.image_singleton]
    exact J.exists_faceLink_singleton_sphere_homeomorph_of_interior hJ hpJ hintJ
  obtain ⟨hmodel⟩ := hmodelJ
  have hmodelS : Nonempty ((S.faceLink {p}).space ≃ₜ Metric.sphere (0 : V3) 1) :=
    ⟨(hface.faceLinkHomeomorphEmbeddedImage hinj hS hsS).trans hmodel⟩
  have hSl : S.faceLink {p} = K.faceLink {p} := by
    change (K.closedStar p).faceLink {p} = K.faceLink {p}
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.Subset.refl _)
  rwa [hSl] at hmodelS

end PoincareConjecture.M76
