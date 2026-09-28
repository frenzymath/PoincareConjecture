import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedSurfaceEdgePosition
import PoincareConjecture.Proofs.M76.PrimeReduction.TransverseSurfaceEdgeCharts

set_option autoImplicit false

open Set Module

namespace Geometry.SimplicialComplex

theorem exists_protected_surface_edge_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 3)
    (J P P₀ T : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite)
    (hP₀ : P₀.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    (hcard : ∀ s ∈ P.faces, s.card ≤ 3)
    (hvertices : Disjoint P₀.space T.vertices)
    (hedges : ∀ t ∈ T.faces, t.card = 2 →
      (P₀.space ∩ convexHull ℝ (t : Set E)).Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (H : PLCarrierMotion J.space P₀.space ε) (A : SimplicialComplex ℝ E),
      A.faces.Finite ∧ A.space = H.map 1 '' P.space ∧
      (∀ s ∈ A.faces, s.card ≤ 3) ∧
      (∀ s ∈ A.faces,
        convexHull ℝ (s : Set E) ⊆ P₀.space ∨
          ∀ t ∈ T.faces, affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
              (convexHull ℝ (t : Set E))) ∧
      Disjoint A.space T.vertices ∧
      (∀ t ∈ T.faces, t.card ≤ 2 →
        (A.space ∩ convexHull ℝ (t : Set E)).Finite) ∧
      {x | x ∈ A.space ∧ ∃ t ∈ T.faces, t.card ≤ 2 ∧
        x ∈ convexHull ℝ (t : Set E)}.Finite ∧
      ∀ t ∈ T.faces, t.card = 2 →
        ∀ p ∈ A.space ∩ convexHull ℝ (t : Set E), p ∉ P₀.space →
          ∃ (U : Set E) (F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E),
            IsOpen U ∧ p ∈ U ∧ F 0 = p ∧
              (∀ z, F z ∈ U → (F z ∈ A.space ↔ z.2 = 0)) ∧
              ∀ z, F z ∈ U → (F z ∈ convexHull ℝ (t : Set E) ↔ z.1 = 0) := by
  obtain ⟨H, A, hA, hAs, hAc, hpos, hAv, hAe, hfinite⟩ :=
    exists_protected_surface_edge_position hdim J P P₀ T hJ hP hP₀ hT
      hcv hP₀P hPJ hfront hcard hvertices hedges hε
  refine ⟨H, A, hA, hAs, hAc, hpos, hAv, hAe, hfinite, ?_⟩
  intro t ht htc p hp hpZ
  exact A.exists_transverse_surface_edge_chart T hA hT hdim hAc hAv hpos
    ht htc hp.1 hp.2 hpZ

end Geometry.SimplicialComplex
