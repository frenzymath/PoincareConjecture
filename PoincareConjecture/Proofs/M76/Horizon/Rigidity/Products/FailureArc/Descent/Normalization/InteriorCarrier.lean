import PoincareConjecture.Proofs.M76.Dehn.OriginalBranchCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProperFaceHalfCarrier
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ScalarPairSubcomplex











set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}






theorem Step.exists_interior_surface_face_carrier
    {s t : Stage e S f r C} (step : Step s t)
    (K K₀ : SimplicialComplex ℝ V) {σ : Finset V} (hσ : σ ∈ K.faces)
    {boundary : Set V} (hrim : boundary ⊆ K₀.space)
    {R : Set M} {j : V → t.Carrier}
    (hjR : MapsTo j K.space (t.projection ⁻¹' R))
    (hproper : ∀ x ∈ K.space,
      j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ boundary)
    (Q : OpenPartialHomeomorph t.Carrier E)
    (B : OpenPartialHomeomorph s.Carrier E)
    (hval : ∀ y, Q y = B (step.projection (step.inclusion y)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hcv : Convex ℝ J.space)
    (hface : ∀ x ∈ convexHull ℝ (σ : Set V),
      j x ∈ Q.source ∧ Q (j x) ∈ interior J.space)
    (hmodel : B.source ⊆ interior (s.projection ⁻¹' R) ∨
      ∃ ell : E →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
        (∀ y ∈ B.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B y)) ∧
        ∀ y ∈ B.source, y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B y) = 0) :
    ∃ L : SimplicialComplex ℝ E,
      L.faces.Finite ∧ Convex ℝ L.space ∧ L.space ⊆ J.space ∧
      (∀ x ∈ convexHull ℝ (σ : Set V),
        x ∉ K₀.space → Q (j x) ∈ interior L.space) ∧
      ((L.space = J.space ∧ Q.source ⊆ interior (t.projection ⁻¹' R)) ∨
        ∃ ell : E →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
          L.space = J.space ∩ {z | 0 ≤ ell z} ∧
          (∀ y ∈ Q.source, y ∈ t.projection ⁻¹' R ↔ 0 ≤ ell (Q y)) ∧
          ∀ y ∈ Q.source,
            y ∈ frontier (t.projection ⁻¹' R) ↔ ell (Q y) = 0) := by
  rcases hmodel with hinside | ⟨ell, hell, hhalf, hfront⟩
  · refine ⟨J, hJ, hcv, Subset.rfl, fun x hx _ => (hface x hx).2,
      Or.inl ⟨rfl, ?_⟩⟩
    intro y hy
    have hp : y ∈ interior
        ((step.projection ∘ step.inclusion) ⁻¹' (s.projection ⁻¹' R)) :=
      preimage_interior_subset_interior_preimage
        (step.projection.continuous.comp step.inclusion.continuous) (hinside (hmaps hy))
    rw [← step.region_preimage R] at hp
    exact hp
  · obtain ⟨L, _, hL, _, hLs, _⟩ :=
      J.exists_finite_nonnegative_zero_pair hJ ell.toAffineMap
    have hupper : ∀ y ∈ Q.source,
        y ∈ t.projection ⁻¹' R ↔ 0 ≤ ell (Q y) := by
      intro y hy
      rw [step.region_preimage R]
      change step.projection (step.inclusion y) ∈ s.projection ⁻¹' R ↔ _
      rw [hval y]
      exact hhalf _ (hmaps hy)
    have hupperfront : ∀ y ∈ Q.source,
        y ∈ frontier (t.projection ⁻¹' R) ↔ ell (Q y) = 0 := by
      intro y hy
      rw [step.frontier_preimage R]
      change step.projection (step.inclusion y) ∈ frontier (s.projection ⁻¹' R) ↔ _
      rw [hval y]
      exact hfront _ (hmaps hy)
    have hLcv : Convex ℝ L.space := by
      rw [hLs]
      exact hcv.inter ((convex_Ici (0 : ℝ)).affine_preimage ell.toAffineMap)
    refine ⟨L, hL, hLcv, hLs.subset.trans inter_subset_left, ?_,
      Or.inr ⟨ell, hell, hLs, hupper, hupperfront⟩⟩
    exact Q.free_source_inside_half_carrier ell hLs (K.convexHull_subset_space hσ)
      hrim hjR hproper (fun x hx => (hface x hx).1) hupper hupperfront
      (fun x hx => (hface x hx).2)

end Geometry.OriginalPLTower
