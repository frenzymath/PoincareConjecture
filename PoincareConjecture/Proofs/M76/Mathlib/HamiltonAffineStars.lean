import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLGraphEmbedding
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLImage
import Mathlib.Topology.Homeomorph.Lemmas
import PoincareConjecture.Proofs.M76.Mathlib.AffineChartStarSubdivision










set_option autoImplicit false

open Set Geometry Topology

namespace ChartedSpace

variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M]

open scoped Classical in






theorem exists_finite_geometric_affine_star_triangulation
    (hlocal : OpenPartialHomeomorph.HasSupportedPLOverlapStraightening
      (M := M) (E := E)) :
    ∃ (s : Finset (OpenPartialHomeomorph M E))
      (K : SimplicialComplex ℝ (s → ℝ × E)), K.faces.Finite ∧
      (∀ p : s → ℝ × E, {p} ∈ K.faces →
        ∃ a : (s → ℝ × E) →ᴬ[ℝ] E,
          InjOn a (K.closedFaceStar {p}).space ∧
          a p ∈ interior (a '' (K.closedFaceStar {p}).space)) ∧
      Nonempty (M ≃ₜ K.space) := by
  classical
  obtain ⟨s, F, U, hF, hFPL, hU, hUs, hcover, hproj⟩ :=
    exists_finite_locallyPL_embedding_with_chart_projections hlocal
  have hchartcover (x : M) : ∃ i : s, x ∈ (i : OpenPartialHomeomorph M E).source := by
    obtain ⟨i, hxi⟩ := hcover x
    exact ⟨i, hUs i hxi⟩
  obtain ⟨K, hK, hKs⟩ :=
    OpenPartialHomeomorph.exists_finite_triangulation_range_of_locallyPL
      (fun i : s => (i : OpenPartialHomeomorph M E)) F hF.injective hchartcover hFPL
  let H : M ≃ₜ K.space :=
    hF.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hKs.symm)
  have hHF (y : K.space) : F (H.symm y) = (y : s → ℝ × E) :=
    congrArg Subtype.val (H.apply_symm_apply y)
  let a : s → (s → ℝ × E) →ᴬ[ℝ] E := fun i =>
    ((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.proj i)).toContinuousAffineMap
  have ha (i : s) (y : K.space) (hy : H.symm y ∈ U i) :
      (i : OpenPartialHomeomorph M E) (H.symm y) = a i y := by
    have heq := hproj i hy
    change (F (H.symm y) i).2 = (i : OpenPartialHomeomorph M E) (H.symm y) at heq
    rw [hHF y] at heq
    exact heq.symm
  obtain ⟨L, hL, hLK, hstars⟩ := K.exists_finite_subdivision_affine_vertex_stars hK H.symm
    (fun i : s => (i : OpenPartialHomeomorph M E)) U hU hUs hcover a ha
  refine ⟨s, L, hL, ?_, ⟨H.trans (Homeomorph.setCongr hLK.space_eq.symm)⟩⟩
  intro p hp
  obtain ⟨i, hinj, hint⟩ := hstars p hp
  exact ⟨a i, hinj, hint⟩

end ChartedSpace
