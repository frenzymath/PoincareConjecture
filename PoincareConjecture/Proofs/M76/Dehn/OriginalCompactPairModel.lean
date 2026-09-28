import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryDefiningCut
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ScalarPairSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLScalarNeighborhoodModel












set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M] [T2Space M]
  [LocallyCompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_compact_original_PL_pair_model
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {R A : Set M} (hR : IsClosed R) (hA : IsCompact A) (hAR : A ⊆ R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (s : Finset A) (G : M → (s → ℝ × E) × ℝ) (C : Set M)
      (P Z : SimplicialComplex ℝ ((s → ℝ × E) × ℝ))
      (H : (C ∩ R : Set M) ≃ₜ P.space),
      IsCompact C ∧ A ⊆ interior C ∧ P.faces.Finite ∧ Z ≤ P ∧
      Continuous G ∧
      (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
      P.space = G '' (C ∩ R) ∧ Z.space = G '' (C ∩ frontier R) ∧
      (∀ x : (C ∩ R : Set M), (H x : (s → ℝ × E) × ℝ) = G x) ∧
      (∀ x : (C ∩ R : Set M), (H x : (s → ℝ × E) × ℝ) ∈ Z.space ↔
        (x : M) ∈ frontier R) ∧
      ∀ x ∈ C, ∃ (i : ι) (V : Set M) (a : ((s → ℝ × E) × ℝ) →ᴬ[ℝ] E),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ G) (e i) V := by
  classical
  obtain ⟨r, W, hW, hAW, hr, hrPL, hcut⟩ :=
    exists_PL_defining_cut_near_compact e hcompat hcover hA hAR hboundary
  obtain ⟨s, G, C, K, H₀, hC, hAC, hCW, hK, hG, hGPL, hscalar,
      hKG, hHG, hcharts⟩ :=
    exists_compact_PL_scalar_neighborhood_model e hcompat hcover hr hrPL hA hW hAW
  let ell : ((s → ℝ × E) × ℝ) →ᵃ[ℝ] ℝ :=
    (LinearMap.snd ℝ (s → ℝ × E) ℝ).toAffineMap
  have hell (x : M) : ell (G x) = r x := hscalar x
  obtain ⟨P, Z, hP, hZP, hPs, hZs⟩ := K.exists_finite_nonnegative_zero_pair hK ell
  have hPi : P.space = G '' (C ∩ R) := by
    rw [hPs, hKG]
    ext z
    constructor
    · rintro ⟨⟨x, hxC, rfl⟩, hx⟩
      change 0 ≤ ell (G x) at hx
      rw [hell] at hx
      have hxR : x ∈ R := (hcut x (hCW hxC)).1.mpr hx
      exact ⟨x, ⟨hxC, hxR⟩, rfl⟩
    · rintro ⟨x, ⟨hxC, hxR⟩, rfl⟩
      refine ⟨mem_image_of_mem G hxC, ?_⟩
      change 0 ≤ ell (G x)
      rw [hell]
      exact (hcut x (hCW hxC)).1.mp hxR
  have hZi : Z.space = G '' (C ∩ frontier R) := by
    rw [hZs, hKG]
    ext z
    constructor
    · rintro ⟨⟨x, hxC, rfl⟩, hx⟩
      change ell (G x) = 0 at hx
      rw [hell] at hx
      have hxR : x ∈ frontier R := (hcut x (hCW hxC)).2.1.mpr hx
      exact ⟨x, ⟨hxC, hxR⟩, rfl⟩
    · rintro ⟨x, ⟨hxC, hxR⟩, rfl⟩
      refine ⟨mem_image_of_mem G hxC, ?_⟩
      change ell (G x) = 0
      rw [hell]
      exact (hcut x (hCW hxC)).2.1.mp hxR
  have hGinj : InjOn G C := by
    intro x hx y hy hxy
    have he : H₀ ⟨x, hx⟩ = H₀ ⟨y, hy⟩ := Subtype.ext
      ((hHG ⟨x, hx⟩).trans (hxy.trans (hHG ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H₀.injective he)
  let : CompactSpace (C ∩ R : Set M) := isCompact_iff_compactSpace.mp (hC.inter_right hR)
  let H₁ : (C ∩ R : Set M) ≃ₜ G '' (C ∩ R) := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn G (C ∩ R) (hGinj.mono inter_subset_left))
    ((hG.comp continuous_subtype_val).subtype_mk _)
  let H : (C ∩ R : Set M) ≃ₜ P.space := H₁.trans (Homeomorph.setCongr hPi.symm)
  have hH (x : (C ∩ R : Set M)) : (H x : (s → ℝ × E) × ℝ) = G x := rfl
  refine ⟨s, G, C, P, Z, H, hC, hAC, hP, hZP, hG, hGPL, hPi, hZi,
    hH, ?_, hcharts⟩
  intro x
  rw [hH, hZi]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact hGinj hy.1 x.property.1 hyx ▸ hy.2
  · exact fun hx => ⟨x, ⟨x.property.1, hx⟩, rfl⟩

end OpenPartialHomeomorph
