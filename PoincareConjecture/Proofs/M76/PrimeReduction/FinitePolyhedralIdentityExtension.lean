import PoincareConjecture.Proofs.M76.Mathlib.FinitePLClosedExtension
import PoincareConjecture.Proofs.M76.Mathlib.CommonSimplicialRefinement
import PoincareConjecture.Proofs.M76.Mathlib.ConvexStrictHalfspaceClosure

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.closedExtension_finite_on_polyhedron
    {C : Set E} {e : C ≃ₜ C} (he : e.IsFinitePL) (hC : IsClosed C)
    (hfix : ∀ x : C, (x : E) ∈ frontier C → e x = x)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) :
    FinitePiecewiseAffineOn (e.closedExtension hC hfix : E → E) J.space := by
  classical
  let G := e.closedExtension hC hfix
  obtain ⟨f, ⟨K, hK, hKC, hfK⟩, hfe⟩ := he
  have hGf (x : E) (hx : x ∈ C) : G x = f x :=
    (e.closedExtension_apply_mem hC hfix hx).trans (hfe ⟨x, hx⟩)
  have hGoutside : EqOn (G : E → E) id Cᶜ :=
    fun _ hx => e.closedExtension_apply_notMem hC hfix hx
  have hGclosure : EqOn (G : E → E) id (closure Cᶜ) :=
    hGoutside.closure G.continuous continuous_id
  let : Fintype K.faces := hK.fintype
  choose H hH using fun t : K.faces =>
    t.val.exists_affine_halfspaces_convexHull (K.indep t.property)
  let Htotal := Finset.univ.biUnion H
  let N := hJ.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ J.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hJ.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨R, hR, hRJ, _, hRH⟩ :=
    J.exists_subdivision_respectsAffineHyperplanes hJ hN Htotal
  refine ⟨R, hR, hRJ.space_eq, ?_⟩
  intro s hs
  have hsne := R.nonempty_of_mem_faces hs
  let y := s.centroid ℝ id
  have hy : y ∈ convexHull ℝ (s : Set E) := s.centroid_mem_convexHull hsne
  have halign (t : K.faces) (A : E →ᵃ[ℝ] ℝ) (hA : A ∈ H t) :
      (∀ x ∈ convexHull ℝ (s : Set E), A x ≤ 0) ∨
      (∀ x ∈ convexHull ℝ (s : Set E), 0 ≤ A x) :=
    hRH A (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t, hA⟩) s hs
  by_cases hyC : y ∈ C
  · have hyK : y ∈ K.space := hKC.symm ▸ hyC
    obtain ⟨t, ht, hyt⟩ := SimplicialComplex.mem_space_iff.mp hyK
    let t' : K.faces := ⟨t, ht⟩
    have hytH : ∀ A ∈ H t', A y ≤ 0 := by
      rwa [hH t'] at hyt
    have hcontain : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
      intro x hx
      rw [hH t']
      intro A hA
      have hside := (halign t' A hA).imp
        (fun h v hv => h v (subset_convexHull ℝ _ hv))
        (fun h v hv => h v (subset_convexHull ℝ _ hv))
      exact s.affine_nonpos_on_hull_of_centroid hsne A hside (hytH A hA) x hx
    obtain ⟨a, ha⟩ := hfK t ht
    refine ⟨a, fun x hx => ?_⟩
    have hxC : x ∈ C := hKC ▸ K.convexHull_subset_space ht (hcontain hx)
    exact (hGf x hxC).trans (ha (hcontain hx))
  · have hpositive (t : K.faces) :
        ∃ A ∈ H t, 0 < A y ∧ ∀ x ∈ convexHull ℝ (s : Set E), 0 ≤ A x := by
      have hnot : ¬∀ A ∈ H t, A y ≤ 0 := by
        intro hall
        apply hyC
        apply hKC.subset
        apply K.convexHull_subset_space t.property
        rw [hH t]
        exact hall
      push Not at hnot
      obtain ⟨A, hA, hAy⟩ := hnot
      rcases halign t A hA with hneg | hpos
      · exact False.elim ((not_le.mpr hAy) (hneg y hy))
      · exact ⟨A, hA, hAy, hpos⟩
    refine ⟨ContinuousAffineMap.id ℝ E, fun x hx => ?_⟩
    have hseg : openSegment ℝ x y ⊆ Cᶜ := by
      rintro z ⟨a, b, ha, hb, hab, rfl⟩ hzC
      have hzK : a • x + b • y ∈ K.space := hKC.symm ▸ hzC
      obtain ⟨t, ht, hzt⟩ := SimplicialComplex.mem_space_iff.mp hzK
      let t' : K.faces := ⟨t, ht⟩
      obtain ⟨A, hA, hAy, hAx⟩ := hpositive t'
      have hnonpos : A (a • x + b • y) ≤ 0 := by
        rw [hH t'] at hzt
        exact hzt A hA
      have hpos : 0 < A (a • x + b • y) := by
        rw [Convex.combo_affine_apply hab]
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (hAx x hx))
          (mul_pos hb hAy)
      exact (not_le.mpr hpos) hnonpos
    exact hGclosure (closure_mono hseg
      (segment_subset_closure_openSegment (left_mem_segment ℝ x y)))

end Homeomorph
