import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.FrontierChartSign

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_frontier_star_inward_coordinates
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (K : SimplicialComplex ℝ E) (g : E → X) (N : Set X)
    (hstars : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (C ∘ g) ∧
      (C.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)))
    (p : E) (hp : p ∈ K.vertices) (hpN : g p ∈ frontier N) :
    ∃ (C : OpenPartialHomeomorph X V3) (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
      (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (C ∘ g) ∧
      ell.contLinear n = 1 ∧
      (∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)) ∧
      ∀ t ∈ K.faces, p ∈ t →
        MapsTo g (convexHull ℝ (t : Set E)) (frontier N) →
        ∃ A : E →ᴬ[ℝ] V3,
          EqOn (C ∘ g) A (convexHull ℝ (t : Set E)) ∧
          ∀ z ∈ convexHull ℝ (t : Set E), ell (A z) = 0 := by
  obtain ⟨C, hcompat, hsource, haff, hside⟩ := hstars p hp
  have hps : p ∈ (K.closedStar p).space := by
    apply (K.closedStar p).convexHull_subset_space (s := {p})
    · exact ⟨K.mem_vertices.mp hp, by simpa using K.mem_vertices.mp hp⟩
    · exact subset_convexHull ℝ _ (by simp)
  have hnot : ¬ C.source ⊆ N := by
    intro hCN
    have hpi : g p ∈ interior N := interior_mono hCN (C.open_source.interior_eq.symm ▸ hsource hps)
    exact hpN.2 hpi
  obtain ⟨ell, n, hn, hside⟩ := hside.resolve_left hnot
  refine ⟨C, ell, n, hcompat, hsource, haff, hn, hside, ?_⟩
  intro t ht hpt hfront
  have htstar : t ∈ (K.closedStar p).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem hpt] using ht⟩
  obtain ⟨A, hA⟩ := haff t htstar
  refine ⟨A, hA, ?_⟩
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz : ell.contLinear n = 0 := congrArg (fun L : V3 →ₗ[ℝ] ℝ => L n) he
    rw [hn] at hz
    norm_num at hz
  have hf := C.isImage_frontier_of_affine_nonneg ell hell hside
  intro z hz
  rw [← hA hz]
  exact (hf.apply_mem_iff (hsource ((K.closedStar p).convexHull_subset_space htstar hz))).mpr
    (hfront hz)

theorem exists_frontier_subcomplex_star_coordinates
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K) (g : E → X) (N : Set X)
    (hgi : InjOn g K.space) (hfront : MapsTo g A.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (C ∘ g) ∧
      (C.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)))
    (p : E) (hp : p ∈ A.vertices) :
    ∃ (C : OpenPartialHomeomorph X V3) (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
      (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (A.closedStar p).space C.source ∧
      (A.closedStar p).AffineOnFaces (C ∘ g) ∧
      InjOn (C ∘ g) (A.closedStar p).space ∧
      ell.contLinear n = 1 ∧
      (∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y)) ∧
      ∀ z ∈ (A.closedStar p).space, ell (C (g z)) = 0 := by
  have hpK : p ∈ K.vertices := K.mem_vertices.mpr (hAK (A.mem_vertices.mp hp))
  obtain ⟨C, ell, n, hcompat, hsource, haff, hn, hside, _⟩ :=
    exists_frontier_star_inward_coordinates e K g N hstars p hpK
      (hfront (A.vertices_subset_space hp))
  have hstarle : A.closedStar p ≤ K.closedStar p := fun _ hs => ⟨hAK hs.1, hAK hs.2⟩
  have hstarA : A.closedStar p ≤ A := fun _ hs => hs.1
  have hsourceA : MapsTo g (A.closedStar p).space C.source :=
    fun _ hz => hsource (Geometry.SimplicialComplex.space_subset_of_le hstarle hz)
  have hiA : InjOn (C ∘ g) (A.closedStar p).space := by
    intro x hx y hy he
    exact hgi (Geometry.SimplicialComplex.space_subset_of_le (hstarA.trans hAK) hx)
      (Geometry.SimplicialComplex.space_subset_of_le (hstarA.trans hAK) hy)
      (C.injOn (hsourceA hx) (hsourceA hy) he)
  refine ⟨C, ell, n, hcompat, hsourceA, fun t ht => haff t (hstarle ht), hiA, hn, hside, ?_⟩
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz : ell.contLinear n = 0 := congrArg (fun L : V3 →ₗ[ℝ] ℝ => L n) he
    rw [hn] at hz
    norm_num at hz
  have hf := C.isImage_frontier_of_affine_nonneg ell hell hside
  intro z hz
  exact (hf.apply_mem_iff (hsourceA hz)).mpr
    (hfront (Geometry.SimplicialComplex.space_subset_of_le hstarA hz))

end PoincareConjecture.M76
