import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.CommonSimplicialRefinement
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionHomeomorph

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.on_finite_polyhedron_of_continuousOn_eq_affine_off
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (hcont : ContinuousOn f L.space) (a : E →ᴬ[ℝ] F)
    (hoff : ∀ x ∈ L.space, x ∉ S → f x = a x) :
    FinitePiecewiseAffineOn f L.space := by
  classical
  obtain ⟨K, hK, rfl, hfK⟩ := hf
  let : Fintype K.faces := hK.fintype
  choose H hH using fun i : K.faces =>
    i.val.exists_affine_halfspaces_convexHull (K.indep i.property)
  let Htotal := Finset.univ.biUnion H
  let N := hL.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ L.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hL.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨R, hR, hRL, _, hRH⟩ :=
    L.exists_subdivision_respectsAffineHyperplanes hL hN Htotal
  refine ⟨R, hR, hRL.space_eq, fun s hs => ?_⟩
  have hsne := R.nonempty_of_mem_faces hs
  let p := s.centroid ℝ id
  have hp : p ∈ convexHull ℝ (s : Set E) := s.centroid_mem_convexHull hsne
  by_cases hpK : p ∈ K.space
  · obtain ⟨t, ht, hpt⟩ := SimplicialComplex.mem_space_iff.mp hpK
    let i : K.faces := ⟨t, ht⟩
    have hsub : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
      intro x hx
      have hptH : ∀ A ∈ H i, A p ≤ 0 := by rwa [hH i] at hpt
      rw [hH i]
      intro A hA
      have hAtotal : A ∈ Htotal :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hA⟩
      have hside := (hRH A hAtotal s hs).imp
        (fun h z hz => h z (subset_convexHull ℝ _ hz))
        (fun h z hz => h z (subset_convexHull ℝ _ hz))
      exact s.affine_nonpos_on_hull_of_centroid hsne A hside (hptH A hA) x hx
    obtain ⟨b, hb⟩ := hfK t ht
    exact ⟨b, fun x hx => hb (hsub hx)⟩
  · refine ⟨a, fun x hx => ?_⟩
    have hsegment : openSegment ℝ p x ⊆ K.spaceᶜ := by
      intro y hy hyK
      obtain ⟨t, ht, hyt⟩ := SimplicialComplex.mem_space_iff.mp hyK
      let i : K.faces := ⟨t, ht⟩
      have hpnot : p ∉ convexHull ℝ (t : Set E) :=
        fun h => hpK (K.convexHull_subset_space ht h)
      have hpnotH : ¬ ∀ A ∈ H i, A p ≤ 0 := by rwa [hH i] at hpnot
      push Not at hpnotH
      obtain ⟨A, hA, hAp⟩ := hpnotH
      have hAtotal : A ∈ Htotal :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hA⟩
      have hAx : 0 ≤ A x := by
        rcases hRH A hAtotal s hs with hnonpos | hnonneg
        · exact (not_le_of_gt hAp (hnonpos p hp)).elim
        · exact hnonneg x hx
      have hyH : ∀ B ∈ H i, B y ≤ 0 := by rwa [hH i] at hyt
      have hAy := hyH A hA
      rw [openSegment_eq_image_lineMap] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring'] at hAy
      have hpositive := mul_pos (sub_pos.mpr hr.2) hAp
      have hnonneg := mul_nonneg hr.1.le hAx
      nlinarith
    have hsegL : segment ℝ p x ⊆ L.space := by
      intro y hy
      rw [← hRL.space_eq]
      exact R.convexHull_subset_space hs ((convex_convexHull ℝ _).segment_subset hp hx hy)
    have hfixed : EqOn f a (openSegment ℝ p x) := fun z hz =>
      hoff z (hsegL (openSegment_subset_segment ℝ p x hz)) (hsegment hz)
    exact hfixed.of_subset_closure (hcont.mono hsegL) a.continuous.continuousOn
      (openSegment_subset_segment ℝ p x) segment_subset_closure_openSegment
      (right_mem_segment ℝ p x)

theorem FinitePiecewiseAffineOn.on_finite_polyhedron_of_eq_affine_off
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hcont : Continuous f) (a : E →ᴬ[ℝ] F)
    (hoff : ∀ x, x ∉ S → f x = a x)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) :
    FinitePiecewiseAffineOn f L.space :=
  hf.on_finite_polyhedron_of_continuousOn_eq_affine_off L hL hcont.continuousOn a
    (fun x _ hx => hoff x hx)

theorem FinitePiecewiseAffineOn.homeomorph_on_finite_polyhedron_of_eq_id_off
    {H : E ≃ₜ E} {S : Set E} (hH : FinitePiecewiseAffineOn (H : E → E) S)
    (hoff : ∀ x, x ∉ S → H x = x)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) :
    FinitePiecewiseAffineOn (H : E → E) L.space :=
  hH.on_finite_polyhedron_of_eq_affine_off H.continuous
    (ContinuousAffineMap.id ℝ E) hoff L hL

end Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem finitePiecewiseAffineOn_symm_of_forall_finite_polyhedron (H : E ≃ₜ F)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → F) K.space)
    (L : SimplicialComplex ℝ F) (hL : L.faces.Finite) :
    FinitePiecewiseAffineOn (H.symm : F → E) L.space := by
  have hcompact : IsCompact (H ⁻¹' L.space) :=
    H.isCompact_preimage.mpr (L.isCompact_space_of_finite hL)
  obtain ⟨K, hK, hpreK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hcompact
      isOpen_univ (subset_univ _)
  have hinv : FinitePiecewiseAffineOn (H.symm : F → E) (H '' K.space) :=
    (hH K hK).inverse (fun x _ => H.symm_apply_apply x)
  apply hinv.restrict L hL
  intro y hy
  refine ⟨H.symm y, interior_subset (hpreK ?_), H.apply_symm_apply y⟩
  change H (H.symm y) ∈ L.space
  rwa [H.apply_symm_apply]

end Homeomorph

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsFinitePLBallPair.image_of_finitePL_on_finite_polyhedra
    {s b : Set E} (hs : IsFinitePLBallPair F s b) (H : E ≃ₜ E)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space) :
    IsFinitePLBallPair F (H '' s) (H '' b) := by
  have hcopy := hs
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hHs := hH K hK
  rw [hKs] at hHs
  exact hs.image hHs H.injective.injOn

theorem IsFinitePLBallPair.preimage_of_finitePL_on_finite_polyhedra
    {s b : Set E} (hs : IsFinitePLBallPair F s b) (H : E ≃ₜ E)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space) :
    IsFinitePLBallPair F (H ⁻¹' s) (H ⁻¹' b) := by
  simpa only [H.image_symm] using hs.image_of_finitePL_on_finite_polyhedra H.symm
    (H.finitePiecewiseAffineOn_symm_of_forall_finite_polyhedron hH)

theorem IsFinitePLBallPair.image_of_finitePL_eq_id_off
    {s b S : Set E} (hs : IsFinitePLBallPair F s b) (H : E ≃ₜ E)
    (hH : FinitePiecewiseAffineOn (H : E → E) S)
    (hoff : ∀ x, x ∉ S → H x = x) :
    IsFinitePLBallPair F (H '' s) (H '' b) := by
  have hcopy := hs
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hHs := hH.homeomorph_on_finite_polyhedron_of_eq_id_off hoff K hK
  rw [hKs] at hHs
  exact hs.image hHs H.injective.injOn

theorem IsFinitePLBallPair.preimage_of_finitePL_eq_id_off
    {s b S : Set E} (hs : IsFinitePLBallPair F s b) (H : E ≃ₜ E)
    (hH : FinitePiecewiseAffineOn (H : E → E) S)
    (hoff : ∀ x, x ∉ S → H x = x) :
    IsFinitePLBallPair F (H ⁻¹' s) (H ⁻¹' b) := by
  have hinv : FinitePiecewiseAffineOn (H.symm : E → E) (H '' S) :=
    hH.inverse (fun x _ => H.symm_apply_apply x)
  have hinvoff (x : E) (hx : x ∉ H '' S) : H.symm x = x := by
    have hxS : H.symm x ∉ S := by
      intro h
      exact hx ⟨H.symm x, h, H.apply_symm_apply x⟩
    exact (hoff (H.symm x) hxS).symm.trans (H.apply_symm_apply x)
  simpa only [H.image_symm] using hs.image_of_finitePL_eq_id_off H.symm hinv hinvoff

end Set

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isFinitePLBallPair_boundedComplement_image_iff (H : E ≃ₜ E)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space) (S : Set E) :
    IsFinitePLBallPair F (closure (boundedComplement (H '' S))) (H '' S) ↔
      IsFinitePLBallPair F (closure (boundedComplement S)) S := by
  constructor
  · intro hball
    have hpre := hball.preimage_of_finitePL_on_finite_polyhedra H hH
    rw [← H.image_closure_boundedComplement S, H.preimage_image, H.preimage_image] at hpre
    exact hpre
  · intro hball
    have himage := hball.image_of_finitePL_on_finite_polyhedra H hH
    rw [H.image_closure_boundedComplement] at himage
    exact himage

end Homeomorph
