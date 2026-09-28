import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalStarChartImages
import PoincareConjecture.Proofs.M76.PrimeReduction.LocalHalfspaceDensity
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarPurity

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

theorem exists_tetrahedral_coface_of_original_chart_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) :
    ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4 := by
  classical
  intro s hs
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : p ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  obtain ⟨B, hsource, hface, hregion⟩ := hstars p hp
  obtain ⟨hinj, V, hV, hpV, hcase⟩ :=
    exists_original_closedStar_image_neighborhood K hK H g hg hp B hsource hregion
  let a : E → V3 := fun z => B (g z)
  let S := K.closedStar p
  have hS : S.faces.Finite := hK.subset (fun _ ht => ht.1)
  have hsS : s ∈ S.faces := ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  let J := hface.embeddedImage hinj
  have hJ : J.faces.Finite := hface.embeddedImage_finite hinj hS
  have hJs : J.space = a '' S.space := hface.embeddedImage_space hinj
  have hsJ : s.image a ∈ J.faces :=
    (hface.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  obtain ⟨z, hzs, hzV⟩ :=
    (convex_convexHull ℝ (s.image a : Set V3)).intrinsicInterior_inter_open_nonempty
      hV ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hpV⟩
  have hzJ : z ∈ J.space := J.convexHull_subset_space hsJ (intrinsicInterior_subset hzs)
  have hzcl : z ∈ closure (interior J.space) := by
    rw [hJs]
    rcases hcase with hinside | ⟨ell, v, hv, hpatch, hhalf, _⟩
    · exact subset_closure (interior_maximal hinside hV hzV)
    · exact mem_closure_interior_of_affine_halfspace_patch hV ell v hv hpatch hzV
        (hhalf (hJs.subset hzJ))
  obtain ⟨t, ht, htcard, hzt⟩ := J.exists_full_face_of_mem_closure_interior hJ hzcl
  have hst := J.subset_of_mem_intrinsicInterior_face hsJ ht hzs hzt
  rw [hface.embeddedImage_faces hinj] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  refine ⟨u, hu.1, ?_, ?_⟩
  · intro v hvs
    obtain ⟨w, hwu, hwv⟩ := Finset.mem_image.mp
      (hst (Finset.mem_image.mpr ⟨v, hvs, rfl⟩))
    have hwveq := hinj (S.subset_space hu hwu) (S.subset_space hsS hvs) hwv
    exact hwveq ▸ hwu
  · have hcard := (Finset.card_image_iff.mpr (hinj.mono (S.subset_space hu))).symm.trans htcard
    simpa using hcard

end PoincareConjecture.M76
