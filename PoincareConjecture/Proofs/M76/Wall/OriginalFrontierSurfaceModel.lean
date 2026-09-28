import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryLinks
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalDomainCharts
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3}

open Classical in

theorem PLDomain.exists_original_frontier_surface_model
    {N : Set X} (he : PLDomain e N) (hN : IsCompact N) (hNne : N.Nonempty) :
    ∃ (s : Finset N) (F : X → (s → ℝ × V3))
      (K A : SimplicialComplex ℝ (s → ℝ × V3))
      (H : N ≃ₜ K.space) (g : (s → ℝ × V3) → N)
      (HB : A.space ≃ₜ frontier N),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ A ≤ K ∧ A.faces.Finite ∧
      (∀ t ∈ K.faces, (∀ p ∈ t, p ∈ A.vertices) → t ∈ A.faces) ∧
      K.space = F '' N ∧ A.space = F '' frontier N ∧
      (∀ x : N, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      (∀ z : A.space, (HB z : X) = (g z : X)) ∧
      (∀ x : frontier N, (HB.symm x : s → ℝ × V3) =
        (H ⟨x, he.closed.frontier_subset x.property⟩ : s → ℝ × V3)) ∧
      (∀ z ∈ K.space, (g z : X) ∈ frontier N ↔ z ∈ A.space) ∧
      (∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
        (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
        (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y))) ∧
      (∀ t ∈ A.faces, ∃ u ∈ A.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ A.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ A.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨s, F, K0, A0, H0, hFc, hFPL, hK0, hA0K, hA0, hK0s,
    hA0s, hH0, _, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair
      e he.compatible he.cover hN he.halfspace
  obtain ⟨x0, hx0⟩ := hNne
  obtain ⟨g, hgc0, hg0, hgPL0⟩ :=
    exists_polyhedral_PL_model_inverse e K0 hK0 H0 F (Subset.refl N)
      ⟨x0, hx0⟩ hH0 hproj
  choose B hpoint hcompat hkind using fun q : K0.space =>
    he.exists_local_region_chart (g q)
  obtain ⟨K, marks, hK, hKK0, hmarks, hstars⟩ :=
    hgPL0.exists_full_compatible_chart_stars K0 hK0 B hcompat hpoint
      (fun _ : Unit => A0) (fun _ => hA0)
      (fun _ => SimplicialComplex.space_subset_of_le hA0K)
  let A := marks ()
  let H : N ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hHF (x : N) : (H x : s → ℝ × V3) = F x := hH0 x
  have hAK : A ≤ K := (hmarks ()).1
  have hAs : A.space = F '' frontier N := (hmarks ()).2.1.trans hA0s
  have hgc : ContinuousOn g K.space := by
    simpa only [hKK0.space_eq] using hgc0
  have hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space := by
    simpa only [hKK0.space_eq] using hgPL0
  have hg (z : K.space) : (g z : X) = (H.symm z : X) :=
    hg0 ⟨z, hKK0.space_eq ▸ z.property⟩
  have hboundary (z : s → ℝ × V3) (hz : z ∈ K.space) :
      (g z : X) ∈ frontier N ↔ z ∈ A.space := by
    rw [hAs]
    exact original_model_mem_image_iff H F g hHF hg he.closed.frontier_subset ⟨z, hz⟩
  obtain ⟨HB, hHB, hHBinv⟩ := exists_original_boundary_homeomorph
    (SimplicialComplex.space_subset_of_le hAK) he.closed.frontier_subset
    H g hg hboundary
  have hcharts : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo (fun z => (g z : X)) (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (fun z => C (g z)) ∧
      (C.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)) := by
    intro p hp
    obtain ⟨q, hsource, hface⟩ := hstars p hp
    refine ⟨B q, hcompat q, hsource, hface, ?_⟩
    rcases hkind q with hinside | ⟨ell, v, hv, _, hhalf⟩
    · exact Or.inl hinside
    · exact Or.inr ⟨ell, v, hv, hhalf⟩
  obtain ⟨hpure, hcounts, hlinks⟩ := original_boundary_surface_incidence
    K A hK hAK he.closed.frontier_subset H g hg hboundary
      (fun p hp => by
        obtain ⟨C, _, hsource, hface, hkind⟩ := hcharts p hp
        exact ⟨C, hsource, hface, hkind⟩)
  refine ⟨s, F, K, A, H, g, HB, hFc, hFPL, hK, hAK, hK.subset hAK,
    (hmarks ()).2.2, hKK0.space_eq.trans hK0s, hAs, hHF, hgc, hg,
    hgPL, hHB, hHBinv, hboundary, hcharts, hpure, ?_, hlinks⟩
  intro t ht htcard
  have hlink : (A.faceLink t).vertices.ncard =
      {u : Finset (s → ℝ × V3) | u ∈ A.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard := by
    simpa only [htcard] using A.ncard_faceLink_vertices_eq_cofaces t
  exact hlink.symm.trans (hcounts t ht htcard)

end PoincareConjecture.M76
