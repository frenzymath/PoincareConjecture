import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedChartSubdivision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateSurface
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem exists_original_marked_surface_finite_incidence_with_rim_polygons
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Nonempty X]
    (e : ι → OpenPartialHomeomorph X V3) (hX : IsCompact (univ : Set X))
    {R S M : Set X} (he : PLDomain e R) (hS : IsCompact S)
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ psi (T y) = 0)) :
    ∃ (s : Finset (univ : Set X)) (F : X → (s → ℝ × V3))
      (K B : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X),
      Continuous F ∧ Function.Injective F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ B ≤ K ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
      K.space = F '' S ∧ B.space = F '' (S ∩ M) ∧
      PolyhedralPLInCharts e g K.space ∧ InjOn g K.space ∧
      (∀ z ∈ K.space, F (g z) = z) ∧ g '' K.space = S ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, q.card = 3 ∧ t ⊆ q) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset (s → ℝ × V3) | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
      HasDisjointPolygonPresentation B.space := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨s, F, N, A, G, hN, hXNint, _, hA, hFc, hF, hG, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_neighborhood_model
      e he.compatible he.cover hX isOpen_univ (subset_univ _)
  have hXN : (univ : Set X) ⊆ N := hXNint.trans interior_subset
  have hNuniv : N = univ := Set.Subset.antisymm (subset_univ _) hXN
  have hFN : Function.Injective F := by
    intro x y hxy
    have hGG : G ⟨x, hXN (mem_univ _)⟩ = G ⟨y, hXN (mem_univ _)⟩ := by
      apply Subtype.ext
      rw [hG, hG]
      exact hxy
    exact congrArg Subtype.val (G.injective hGG)
  have hAs : A.space = F '' N := by
    ext z
    constructor
    · intro hz
      exact ⟨G.symm ⟨z, hz⟩, (G.symm ⟨z, hz⟩).property,
        (hG (G.symm ⟨z, hz⟩)).symm.trans
          (congrArg Subtype.val (G.apply_symm_apply ⟨z, hz⟩))⟩
    · rintro ⟨x, hx, rfl⟩
      rw [← hG ⟨x, hx⟩]
      exact (G ⟨x, hx⟩).property
  have hcharts : ∀ x ∈ S,
      ∃ (T : OpenPartialHomeomorph X V3) (V : Set X)
        (cuts marks : Finset (V3 →ᵃ[ℝ] ℝ)),
        IsOpen V ∧ x ∈ V ∧ V ⊆ T.source ∧
        (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ V, y ∈ S ↔ ∀ a ∈ cuts, a (T y) ≤ 0) ∧
        ∀ y ∈ V, y ∈ M ↔ ∀ a ∈ marks, a (T y) ≤ 0 := by
    intro x hx
    obtain ⟨T, hxT, hcompat, hkind⟩ := hlocal x hx
    rcases hkind with ⟨ell, _, _, hplane, hdis⟩ |
      ⟨ell, psi, _, _, _, _, _, hhalf, hmark⟩
    · refine ⟨T, T.source, {ell.toAffineMap, -ell.toAffineMap},
        {AffineMap.const ℝ V3 (1 : ℝ)}, T.open_source, hxT, Subset.rfl, hcompat, ?_, ?_⟩
      · intro y hy
        rw [hplane y hy]
        simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        change ell (T y) = 0 ↔ ell (T y) ≤ 0 ∧ -ell (T y) ≤ 0
        rw [neg_nonpos]
        exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
      · intro y hy
        have hyM : y ∉ M := fun h => disjoint_left.mp hdis hy h
        simp [hyM]
    · refine ⟨T, T.source, {ell.toAffineMap, -ell.toAffineMap, -psi.toAffineMap},
        {psi.toAffineMap, -psi.toAffineMap}, T.open_source, hxT, Subset.rfl, hcompat, ?_, ?_⟩
      · intro y hy
        rw [hhalf y hy]
        simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        change (ell (T y) = 0 ∧ 0 ≤ psi (T y)) ↔
          ell (T y) ≤ 0 ∧ -ell (T y) ≤ 0 ∧ -psi (T y) ≤ 0
        simp only [neg_nonpos]
        exact ⟨fun h => ⟨h.1.le, h.1.ge, h.2⟩,
          fun h => ⟨le_antisymm h.1 h.2.1, h.2.2⟩⟩
      · intro y hy
        rw [hmark y hy]
        simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        change psi (T y) = 0 ↔ psi (T y) ≤ 0 ∧ -psi (T y) ≤ 0
        rw [neg_nonpos]
        exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  obtain ⟨P, Q, hP, hQ, hPs, hQs⟩ :=
    HamiltonIntervalTorus.exists_compact_marked_polyhedral_image e he.cover hF hS
      hFN.injOn hcharts
  have hPA : P.space ⊆ A.space := by
    rw [hPs, hAs]
    exact image_mono ((subset_univ S).trans hXN)
  have hQP : Q.space ⊆ P.space := by rw [hQs, hPs]; exact image_mono inter_subset_left
  by_cases hXne : Nonempty X
  · let xN : N := ⟨Classical.choice hXne, hXN (mem_univ _)⟩
    obtain ⟨g0, hgc, hg0, hgPL⟩ :=
      exists_polyhedral_PL_model_inverse e A hA G F (Subset.refl N) xN hG hproj
    let g : (s → ℝ × V3) → X := fun z => g0 z
    have hFg (z : s → ℝ × V3) (hz : z ∈ A.space) : F (g z) = z := by
      change F (g0 z) = z
      rw [hg0 ⟨z, hz⟩, ← hG (G.symm ⟨z, hz⟩), G.apply_symm_apply]
    let : CompactSpace S := isCompact_iff_compactSpace.mp hS
    let HS : S ≃ₜ P.space :=
      (Continuous.homeoOfEquivCompactToT2
        (f := Equiv.Set.imageOfInjOn F S hFN.injOn)
        ((hFc.comp continuous_subtype_val).subtype_mk _)).trans (Homeomorph.setCongr hPs.symm)
    have hHS (x : S) : (HS x : s → ℝ × V3) = F x := rfl
    have hHSg (z : P.space) : (HS.symm z : X) = g z := by
      apply hFN
      have hval : F (HS.symm z) = (z : s → ℝ × V3) :=
        (hHS (HS.symm z)).symm.trans (congrArg Subtype.val (HS.apply_symm_apply z))
      exact hval.trans (hFg z (hPA z.property)).symm
    have hgP : PolyhedralPLInCharts e g P.space := hgPL.restrict_finite P hP hPA
    have hQM (z : s → ℝ × V3) (hz : z ∈ P.space) : g z ∈ M ↔ z ∈ Q.space := by
      rw [hQs]
      have hgS : g z ∈ S := by rw [← hHSg ⟨z, hz⟩]; exact (HS.symm ⟨z, hz⟩).property
      constructor
      · intro hzM
        exact ⟨g z, ⟨hgS, hzM⟩, hFg z (hPA hz)⟩
      · rintro ⟨x, hx, hFx⟩
        have hxg := hFN (hFx.trans (hFg z (hPA hz)).symm)
        exact hxg ▸ hx.2
    obtain ⟨K, B, hK, hKP, hBK, hBs, hfull, hpure, hcounts, hlinks, hpolygons⟩ :=
      exists_marked_surface_incidence_subdivision_with_rim_polygons
        e P Q hP hQ hQP HS.symm g hHSg hgP hQM hlocal
    have hKsub : K.space ⊆ A.space := hKP.space_eq.subset.trans hPA
    refine ⟨s, F, K, B, g, hFc, hFN, hF, hK, hBK, hfull,
      hKP.space_eq.trans hPs, hBs.trans hQs,
      hgPL.restrict_finite K hK hKsub, ?_, fun z hz => hFg z (hKsub hz), ?_, ?_,
      hcounts, hlinks, hpolygons⟩
    · intro z hz w hw hzw
      exact (hFg z (hKsub hz)).symm.trans ((congrArg F hzw).trans (hFg w (hKsub hw)))
    · apply Subset.antisymm
      · rintro x ⟨z, hz, rfl⟩
        rw [← hHSg ⟨z, hKP.space_eq ▸ hz⟩]
        exact (HS.symm ⟨z, hKP.space_eq ▸ hz⟩).property
      · intro x hx
        refine ⟨HS ⟨x, hx⟩, hKP.space_eq.symm ▸ (HS ⟨x, hx⟩).property, ?_⟩
        have h := hHSg (HS ⟨x, hx⟩)
        simpa only [HS.symm_apply_apply] using h.symm
    · intro t ht
      obtain ⟨q, hq, htq, hqc⟩ := hpure t ht
      exact ⟨q, hq, hqc, htq⟩
  · exact False.elim (hXne inferInstance)

open Classical in
theorem exists_original_marked_surface_finite_incidence
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Nonempty X]
    (e : ι → OpenPartialHomeomorph X V3) (hX : IsCompact (univ : Set X))
    {R S M : Set X} (he : PLDomain e R) (hS : IsCompact S)
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ psi (T y) = 0)) :
    ∃ (s : Finset (univ : Set X)) (F : X → (s → ℝ × V3))
      (K B : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X),
      Continuous F ∧ Function.Injective F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ B ≤ K ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
      K.space = F '' S ∧ B.space = F '' (S ∩ M) ∧
      PolyhedralPLInCharts e g K.space ∧ InjOn g K.space ∧
      (∀ z ∈ K.space, F (g z) = z) ∧ g '' K.space = S ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, q.card = 3 ∧ t ⊆ q) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset (s → ℝ × V3) | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      ∀ v ∈ K.vertices, IsConnected (K.link v).space := by
  obtain ⟨s, F, K, B, g, hFc, hFi, hF, hK, hBK, hfull, hKs, hBs,
    hPL, hgi, hfg, hgs, hpure, hcounts, hlinks, _⟩ :=
    exists_original_marked_surface_finite_incidence_with_rim_polygons e hX he hS hlocal
  exact ⟨s, F, K, B, g, hFc, hFi, hF, hK, hBK, hfull, hKs, hBs,
    hPL, hgi, hfg, hgs, hpure, hcounts, hlinks⟩


end PoincareConjecture.M76
