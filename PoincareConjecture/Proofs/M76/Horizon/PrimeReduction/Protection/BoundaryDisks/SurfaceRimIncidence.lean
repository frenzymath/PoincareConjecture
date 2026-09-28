import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedChartSubdivision

set_option autoImplicit false
open Set Filter Geometry
open scoped Topology
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

omit [FiniteDimensional ℝ E] in
theorem marked_surface_planar_halfspace_stars_of_rim_equations
    (K B : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {S M : Set X} (H : K.space ≃ₜ S) (g : E → X)
    (hH : ∀ z : K.space, (H z : X) = g z)
    (hB : ∀ z ∈ K.space, g z ∈ M ↔ z ∈ B.space)
    (hcharts : ∀ p ∈ K.vertices, ∃ T : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space T.source ∧
      (K.closedStar p).AffineOnFaces (fun z => T (g z)) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ ell (T y) = 0 ∧ psi (T y) = 0)) :
    ∀ p ∈ K.vertices, ∃ (f : E → V2) (V : Set V2),
      (K.closedStar p).AffineOnFaces f ∧ InjOn f (K.closedStar p).space ∧
      IsOpen V ∧ f p ∈ V ∧
      ((V ⊆ f '' (K.closedStar p).space ∧ Disjoint (K.closedStar p).space B.space) ∨
        ∃ (ell : V2 →ᴬ[ℝ] ℝ) (v : V2), ell.contLinear v = 1 ∧
          V ∩ {z | 0 ≤ ell z} ⊆ f '' (K.closedStar p).space ∧
          f '' (K.closedStar p).space ⊆ {z | 0 ≤ ell z} ∧
          ∀ x ∈ (K.closedStar p).space, x ∈ B.space ↔ ell (f x) = 0) := by
  intro p hp
  obtain ⟨T, hsource, hface, hkind⟩ := hcharts p hp
  have hsub : (K.closedStar p).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hgS (x : E) (hx : x ∈ K.space) : g x ∈ S := by
    rw [← hH ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  rcases hkind with ⟨ell, v, hv, hlocal, hdis⟩ |
    ⟨ell, psi, u, v, hu, hv, huv, hlocal, hmark⟩
  · have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h, LinearMap.zero_apply] at hval
      exact zero_ne_one hval
    obtain ⟨a, r, hra, har, haz⟩ :=
      ell.toAffineMap.exists_zeroLevel_coordinates (F := V2) hell (by simp)
    obtain ⟨hf, hi, V, hV, hpV, hpatch, _⟩ :=
      exists_surface_star_image_patch K hK H g hH hp T hsource hface ell a r hra har haz
        univ (by intro y hy; simpa only [mem_univ, and_true] using hlocal y hy)
    refine ⟨fun z => r (T (g z)), V, hf, hi, hV, hpV, Or.inl ⟨?_, ?_⟩⟩
    · simpa only [inter_univ] using hpatch
    · apply disjoint_left.mpr
      intro x hx hxB
      exact disjoint_left.mp hdis (hsource hx) ((hB x (hsub hx)).mpr hxB)
  · have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h, LinearMap.zero_apply] at hval
      exact zero_ne_one hval
    obtain ⟨a, r, hra, har, haz⟩ :=
      ell.toAffineMap.exists_zeroLevel_coordinates (F := V2) hell (by simp)
    obtain ⟨w, hw⟩ := exists_transverse_hyperplane_coordinate_direction ell psi u v
      hu hv huv a r har haz
    have hlocal' (y : X) (hy : y ∈ T.source) :
        y ∈ S ↔ ell (T y) = 0 ∧ r (T y) ∈ {z | 0 ≤ (psi.comp a) z} := by
      rw [hlocal y hy]
      constructor <;> intro h
      · exact ⟨h.1, by change 0 ≤ psi (a (r (T y))); rw [har h.1]; exact h.2⟩
      · refine ⟨h.1, ?_⟩
        have hh : 0 ≤ psi (a (r (T y))) := h.2
        simpa only [har h.1] using hh
    obtain ⟨hf, hi, V, hV, hpV, hpatch, hhalf⟩ :=
      exists_surface_star_image_patch K hK H g hH hp T hsource hface ell a r hra har haz
        {z | 0 ≤ (psi.comp a) z} hlocal'
    refine ⟨fun z => r (T (g z)), V, hf, hi, hV, hpV,
      Or.inr ⟨psi.comp a, w, hw, hpatch, hhalf, ?_⟩⟩
    intro x hx
    have hz := ((hlocal (g x) (hsource hx)).mp (hgS x (hsub hx))).1
    change x ∈ B.space ↔ psi (a (r (T (g x)))) = 0
    have hm := hmark (g x) (hsource hx)
    simp only [hz, true_and] at hm
    rw [har hz, ← hm]
    exact (hB x (hsub hx)).symm

open Classical in
theorem exists_surface_rim_incidence_subdivision
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
          ∀ y ∈ T.source, y ∈ M ↔ ell (T y) = 0 ∧ psi (T y) = 0)) :
    ∃ K B : SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.IsSubdivision K0 ∧ B ≤ K ∧ B.space = B0.space ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset E | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
      HasDisjointPolygonPresentation B.space := by
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
          ∀ y ∈ C.source, y ∈ M ↔ ell (C y) = 0 ∧ psi (C y) = 0) := by
    intro p hp
    obtain ⟨z, hsource, hface⟩ := hstars p hp
    exact ⟨T z, hsource, hface, hkind z⟩
  obtain ⟨hpure, hcounts, hlinks⟩ :=
    K.marked_surface_incidence_of_planar_halfspace_stars B hK (hmarks ()).1
      (hmarks ()).2.2 (marked_surface_planar_halfspace_stars_of_rim_equations K B hK H g hH hBM hcharts)
  refine ⟨K, B, hK, hKK0, (hmarks ()).1, (hmarks ()).2.1,
    (hmarks ()).2.2, hpure, ?_, ?_, ?_⟩
  · intro t ht htc
    have hc : (K.faceLink t).vertices.ncard =
        {q : Finset E | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard := by
      simpa only [htc] using K.ncard_faceLink_vertices_eq_cofaces t
    exact hc.symm.trans (hcounts t ht htc)
  · intro v hv
    simpa only [K.faceLink_singleton_eq_link] using hlinks v hv
  · exact K.hasDisjointPolygonPresentation_boundary_of_marked_planar_halfspace_stars B hK
      (hmarks ()).1 (hmarks ()).2.2
      (marked_surface_planar_halfspace_stars_of_rim_equations K B hK H g hH hBM hcharts)

end PoincareConjecture.M76
