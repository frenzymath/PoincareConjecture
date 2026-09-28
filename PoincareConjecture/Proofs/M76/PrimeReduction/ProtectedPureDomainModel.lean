import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedDomainChartStars
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartStarPurity

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]

theorem exists_protected_pure_domain_model
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (s → ℝ × V3) → R),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ a, A a ≤ K ∧ (A a).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A a).vertices) → t ∈ (A a).faces) ∧
      K.space = F '' R ∧ (A 0).space = F '' frontier R ∧
      (A 1).space = F '' D ∧ (A 2).space = F '' frontier D ∧
      (∀ x : R, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      (∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4) ∧
      ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
        (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) := by
  classical
  obtain ⟨s, F, K, A, H, g, hFc, hF, hK, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hstars⟩ := exists_protected_domain_chart_stars hR he hDR b
  have hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4 :=
    exists_tetrahedral_coface_of_original_chart_stars K hK H g hg (by
      intro p hp
      obtain ⟨B, hsource, _, hface, hregion⟩ := hstars p hp
      exact ⟨B, hsource, hface, hregion⟩)
  exact ⟨s, F, K, A, H, g, hFc, hF, hK, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hpure, hstars⟩

end PoincareConjecture.M76
