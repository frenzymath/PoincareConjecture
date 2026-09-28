import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.ActualSurfaceStars

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X]

theorem marked_surface_planar_halfspace_stars_of_intrinsic_mark
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
          ∀ y ∈ T.source, y ∈ S → (y ∈ M ↔ psi (T y) = 0))) :
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
    rw [har hz, ← hmark (g x) (hsource hx) (hgS x (hsub hx))]
    exact (hB x (hsub hx)).symm

end PoincareConjecture.M76.HamiltonIntervalTorus
