import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.exists_finite_halfspace_preimage
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (H : Finset (F →ᵃ[ℝ] ℝ)) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = S ∩ {x | ∀ A ∈ H, A (f x) ≤ 0} := by
  classical
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  let : Finite K.faces := hK.to_subtype
  have hpiece (s : K.faces) : ∃ L : SimplicialComplex ℝ E,
      L.faces.Finite ∧ L.space = convexHull ℝ (s.val : Set E) ∩
        {x | ∀ A ∈ H, A (f x) ≤ 0} := by
    obtain ⟨a, ha⟩ := hfaces s.val s.property
    obtain ⟨Hsource, hHsource⟩ :=
      s.val.exists_affine_halfspaces_convexHull (K.indep s.property)
    have hcompact := s.val.finite_toSet.isCompact_convexHull ℝ
    obtain ⟨C, hC, hCs⟩ :=
      hcompact.exists_finite_triangulation_of_halfspaces Hsource hHsource
    let pull := H.image (fun A => A.comp a.toAffineMap)
    obtain ⟨L, hL, hLs⟩ := C.exists_finite_triangulation_inter_halfspaces hC pull
    refine ⟨L, hL, hLs.trans ?_⟩
    rw [hCs]
    ext x
    constructor
    · rintro ⟨hx, hconstraints⟩
      refine ⟨hx, fun A hA => ?_⟩
      have h := hconstraints (A.comp a.toAffineMap)
        (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
      change A (a x) ≤ 0 at h
      rwa [← ha hx] at h
    · rintro ⟨hx, hconstraints⟩
      refine ⟨hx, ?_⟩
      intro B hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      change A (a x) ≤ 0
      rw [← ha hx]
      exact hconstraints A hA
  choose L hL hLs using hpiece
  obtain ⟨J, hJ, hJs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion L hL
  refine ⟨J, hJ, hJs.trans ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    rw [hLs s] at hs
    exact ⟨K.convexHull_subset_space s.property hs.1, hs.2⟩
  · rintro ⟨hx, hconstraints⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    refine mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩
    rw [hLs]
    exact ⟨hxs, hconstraints⟩

theorem FinitePiecewiseAffineOn.exists_finite_fiber_complex
    [FiniteDimensional ℝ F] {f : E → F} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) (c : F) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = S ∩ {x | f x = c} := by
  classical
  obtain ⟨H, hH⟩ := ({c} : Finset F).exists_affine_halfspaces_convexHull
    (affineIndependent_of_subsingleton ℝ _)
  have hconstraints (x : E) : (∀ A ∈ H, A (f x) ≤ 0) ↔ f x = c := by
    change f x ∈ {y | ∀ A ∈ H, A y ≤ 0} ↔ f x = c
    rw [← hH]
    simp only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff]
  obtain ⟨L, hL, hLs⟩ := hf.exists_finite_halfspace_preimage H
  exact ⟨L, hL, hLs.trans (by ext x; simp only [mem_inter_iff,
    mem_ofPred_eq, hconstraints])⟩

theorem FinitePiecewiseAffineOn.exists_finite_product_equalizer
    [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {f : E → G} {g : F → G} {S : Set E} {T : Set F}
    (hf : FinitePiecewiseAffineOn f S) (hg : FinitePiecewiseAffineOn g T) :
    ∃ L : SimplicialComplex ℝ (E × F), L.faces.Finite ∧
      L.space = {z | z.1 ∈ S ∧ z.2 ∈ T ∧ f z.1 = g z.2} := by
  let difference : G × G →ᴬ[ℝ] G :=
    (ContinuousLinearMap.fst ℝ G G - ContinuousLinearMap.snd ℝ G G).toContinuousAffineMap
  have hdiff := (hf.prodMap hg).postcomp difference
  obtain ⟨L, hL, hLs⟩ := hdiff.exists_finite_fiber_complex 0
  refine ⟨L, hL, hLs.trans ?_⟩
  ext z
  change ((z.1 ∈ S ∧ z.2 ∈ T) ∧ f z.1 - g z.2 = 0) ↔
    z.1 ∈ S ∧ z.2 ∈ T ∧ f z.1 = g z.2
  simp only [sub_eq_zero, and_assoc]

end Geometry
