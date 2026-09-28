import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CompactPLDomainImage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronNeighborhoodRetraction
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLNeighborhoodModel

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E G ι : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem exists_finite_PL_domain_image_pair
    (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {F : M → G} (hFc : Continuous F)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    {N : Set M} (hN : IsCompact N) (hinj : InjOn F N)
    (hboundary : ∀ x ∈ frontier N,
      ∃ (psi : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        psi.contLinear v = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ psi (B y)) :
    ∃ (K L : SimplicialComplex ℝ G) (H : N ≃ₜ K.space),
      K.faces.Finite ∧ L ≤ K ∧ L.faces.Finite ∧
      K.space = F '' N ∧ L.space = F '' frontier N ∧
      (∀ x : N, (H x : G) = F x) ∧
      ∀ x : N, (H x : G) ∈ L.space ↔ (x : M) ∈ frontier N := by
  obtain ⟨K, L, hK, hL, hKs, hLs⟩ :=
    exists_finite_triangulations_domain_frontier_image e hcover hF hN hinj hboundary
  have hLK : L.space ⊆ K.space := by
    rw [hLs, hKs]
    exact image_mono hN.isClosed.frontier_subset
  obtain ⟨R, S, hR, hRK, hSR, hSL⟩ :=
    K.exists_subdivision_with_polyhedron_subcomplex L hK hL hLK
  have hRs : R.space = F '' N := hRK.space_eq.trans hKs
  have hSs : S.space = F '' frontier N := hSL.trans hLs
  let : CompactSpace N := isCompact_iff_compactSpace.mp hN
  let H0 : N ≃ₜ F '' N := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn F N hinj)
    ((hFc.comp continuous_subtype_val).subtype_mk _)
  let H : N ≃ₜ R.space := H0.trans (Homeomorph.setCongr hRs.symm)
  have hHF (x : N) : (H x : G) = F x := rfl
  refine ⟨R, S, H, hR, hSR, hR.subset hSR, hRs, hSs, hHF, ?_⟩
  intro x
  rw [hHF, hSs]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact hinj (hN.isClosed.frontier_subset hy) x.property hyx ▸ hy
  · exact fun hx => mem_image_of_mem F hx

theorem exists_compact_PL_domain_finite_pair [LocallyCompactSpace M]
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {N : Set M} (hN : IsCompact N)
    (hboundary : ∀ x ∈ frontier N,
      ∃ (psi : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        psi.contLinear v = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ psi (B y)) :
    ∃ (s : Finset N) (F : M → (s → ℝ × E))
      (K L : SimplicialComplex ℝ (s → ℝ × E)) (H : N ≃ₜ K.space),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ L ≤ K ∧ L.faces.Finite ∧
      K.space = F '' N ∧ L.space = F '' frontier N ∧
      (∀ x : N, (H x : (s → ℝ × E)) = F x) ∧
      (∀ x : N, (H x : (s → ℝ × E)) ∈ L.space ↔ (x : M) ∈ frontier N) ∧
      ∀ x ∈ N, ∃ (i : ι) (V : Set M) (a : (s → ℝ × E) →ᴬ[ℝ] E),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  obtain ⟨s, F, C, J, H, _, hNC, _, _, hFc, hFPL, hHF, hproj⟩ :=
    exists_compact_PL_neighborhood_model e hcompat hcover hN isOpen_univ (subset_univ _)
  have hFinj : InjOn F C := by
    intro x hx y hy hxy
    have he : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective he)
  obtain ⟨K, L, T, hK, hLK, hL, hKs, hLs, hTF, hbound⟩ :=
    exists_finite_PL_domain_image_pair e hcover hFc hFPL hN
      (hFinj.mono (hNC.trans interior_subset)) hboundary
  exact ⟨s, F, K, L, T, hFc, hFPL, hK, hLK, hL, hKs, hLs, hTF, hbound,
    fun x hx => hproj x (interior_subset (hNC hx))⟩

end OpenPartialHomeomorph
