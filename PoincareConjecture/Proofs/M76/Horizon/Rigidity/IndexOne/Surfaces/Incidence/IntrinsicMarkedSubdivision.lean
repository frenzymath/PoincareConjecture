import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Incidence.IntrinsicMarkedStars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.PlanarStarIncidence
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

open Classical in
theorem exists_marked_surface_incidence_subdivision_of_intrinsic_mark
    (e : ι → OpenPartialHomeomorph X V3)
    (K0 B0 : SimplicialComplex ℝ E) (hK0 : K0.faces.Finite) (hB0 : B0.faces.Finite)
    (hB0K : B0.space ⊆ K0.space)
    {S M : Set X} (H0 : K0.space ≃ₜ S) (g : E → X)
    (hH0 : ∀ z : K0.space, (H0 z : X) = g z)
    (hgPL : PolyhedralPLInCharts e g K0.space)
    (hB0M : ∀ z ∈ K0.space, g z ∈ M ↔ z ∈ B0.space)
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ S → (y ∈ M ↔ psi (T y) = 0))) :
    ∃ K B : SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.IsSubdivision K0 ∧ B ≤ K ∧ B.space = B0.space ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset E | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      ∀ v ∈ K.vertices, IsConnected (K.link v).space := by
  classical
  have hgS (z : K0.space) : g z ∈ S := by
    rw [← hH0 z]
    exact (H0 z).property
  choose T hpoint hcompat hkind using fun z : K0.space => hlocal (g z) (hgS z)
  obtain ⟨K, marks, hK, hKK0, hmarks, hstars⟩ :=
    hgPL.exists_full_compatible_chart_stars K0 hK0 T hcompat hpoint
      (fun _ : Unit => B0) (fun _ => hB0) (fun _ => hB0K)
  let B := marks ()
  let H : K.space ≃ₜ S := (Homeomorph.setCongr hKK0.space_eq).trans H0
  have hH (z : K.space) : (H z : X) = g z := hH0 ⟨z, hKK0.space_eq ▸ z.property⟩
  have hBM (z : E) (hz : z ∈ K.space) : g z ∈ M ↔ z ∈ B.space := by
    rw [(hmarks ()).2.1]
    exact hB0M z (hKK0.space_eq ▸ hz)
  have hcharts : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (fun z => C (g z)) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ C.source, y ∈ S ↔ ell (C y) = 0) ∧ Disjoint C.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ C.source, y ∈ S ↔ ell (C y) = 0 ∧ 0 ≤ psi (C y)) ∧
          ∀ y ∈ C.source, y ∈ S → (y ∈ M ↔ psi (C y) = 0)) := by
    intro p hp
    obtain ⟨z, hsource, hface⟩ := hstars p hp
    exact ⟨T z, hsource, hface, hkind z⟩
  obtain ⟨hpure, hcounts, hlinks⟩ :=
    K.marked_surface_incidence_of_planar_halfspace_stars B hK (hmarks ()).1
      (hmarks ()).2.2 (marked_surface_planar_halfspace_stars_of_intrinsic_mark K B hK H g hH hBM hcharts)
  refine ⟨K, B, hK, hKK0, (hmarks ()).1, (hmarks ()).2.1,
    (hmarks ()).2.2, hpure, ?_, ?_⟩
  · intro t ht htc
    have hc : (K.faceLink t).vertices.ncard =
        {q : Finset E | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard := by
      simpa only [htc] using K.ncard_faceLink_vertices_eq_cofaces t
    exact hc.symm.trans (hcounts t ht htc)
  · intro v hv
    simpa only [K.faceLink_singleton_eq_link] using hlinks v hv

end PoincareConjecture.M76.HamiltonIntervalTorus
