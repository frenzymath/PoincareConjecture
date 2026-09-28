import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartSurfaceMotion
import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedSurfaceEdgeCharts

set_option autoImplicit false

open Set Geometry Module

namespace PoincareConjecture.M76

theorem exists_original_chart_surface_position
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (hdim : finrank ℝ E = 3)
    (e : ι → OpenPartialHomeomorph X E)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (B : OpenPartialHomeomorph X E)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E)
    (J P P₀ T : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite)
    (hP₀ : P₀.faces.Finite) (hT : T.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space) (hJB : J.space ⊆ B.target)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    (hcard : ∀ s ∈ P.faces, s.card ≤ 3)
    (hvertices : Disjoint P₀.space T.vertices)
    (hedges : ∀ t ∈ T.faces, t.card = 2 →
      (P₀.space ∩ convexHull ℝ (t : Set E)).Finite)
    (S : Set X) (hlocal : ∀ x ∈ J.space, B.symm x ∈ S ↔ x ∈ P.space)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (H : PLCarrierMotion J.space P₀.space ε)
      (A : SimplicialComplex ℝ E) (Phi : X ≃ₜ X),
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
      (∀ x ∈ B.target, Phi (B.symm x) = B.symm (H.map 1 x)) ∧
      EqOn Phi id (B.symm '' J.space)ᶜ ∧ EqOn Phi id (B.symm '' P₀.space) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) ∧
      (∀ x ∈ J.space, B.symm x ∈ Phi '' S ↔ x ∈ A.space) ∧
      ∀ t ∈ T.faces, t.card = 2 →
        ∀ p ∈ A.space ∩ convexHull ℝ (t : Set E),
          p ∈ interior J.space → p ∉ P₀.space →
          ∃ (U : Set E) (F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E),
            IsOpen U ∧ p ∈ U ∧ U ⊆ B.target ∧ U ⊆ interior J.space ∧ F 0 = p ∧
              (∀ z, F z ∈ U → (B.symm (F z) ∈ Phi '' S ↔ z.2 = 0)) ∧
              ∀ z, F z ∈ U → (F z ∈ convexHull ℝ (t : Set E) ↔ z.1 = 0) := by
  obtain ⟨H, A, hA, hAs, hAc, hpos, hAv, hAe, hfinite, hcharts⟩ :=
    SimplicialComplex.exists_protected_surface_edge_charts hdim J P P₀ T
      hJ hP hP₀ hT hcv hP₀P hPJ hfront hcard hvertices hedges hε
  obtain ⟨Phi, hPhiB, hPhiout, hPhiprot, hPhiPL, hPhiinv, hPhiS⟩ :=
    exists_original_chart_surface_motion e he B hB J hJ hJB
      (hP₀P.trans hPJ) H S P.space hlocal
  have hwhole (x : E) (hx : x ∈ J.space) :
      B.symm x ∈ Phi '' S ↔ x ∈ A.space := by
    simpa only [hAs] using hPhiS x hx
  refine ⟨H, A, Phi, hA, hAs, hAc, hpos, hAv, hAe, hfinite,
    hPhiB, hPhiout, hPhiprot, hPhiPL, hPhiinv, hwhole, ?_⟩
  intro t ht htc p hp hpJ hpP₀
  obtain ⟨U, F, hU, hpU, hF, hFA, hFt⟩ := hcharts t ht htc p hp hpP₀
  refine ⟨(U ∩ interior J.space) ∩ B.target, F,
    (hU.inter isOpen_interior).inter B.open_target,
    ⟨⟨hpU, hpJ⟩, hJB (interior_subset hpJ)⟩,
    (fun _ hx => hx.2), (fun _ hx => hx.1.2), hF, ?_, ?_⟩
  · intro z hz
    exact (hwhole (F z) (interior_subset hz.1.2)).trans (hFA z hz.1.1)
  · intro z hz
    exact hFt z hz.1.1

end PoincareConjecture.M76
