import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Polygons.TriangleFiber



set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "I" => Icc (-1 : ℝ) 1

structure SurfaceTriangleFibers (T : CoorientedSurfaceStars E) where
  map : Finset E → ℝ → E
  piecewiseAffine : ∀ s ∈ (T.marked 2).faces, s.card = 3 →
    FinitePiecewiseAffineOn (map s) I
  injective : ∀ s ∈ (T.marked 2).faces, s.card = 3 → InjOn (map s) I
  image_eq : ∀ s ∈ (T.marked 2).faces, s.card = 3 → map s '' I = T.dualRegion s
  central : ∀ s ∈ (T.marked 2).faces, s.card = 3 → map s 0 = s.centroid ℝ id
  rim : ∀ s ∈ (T.marked 2).faces, s.card = 3 → ∀ r ∈ I,
    map s r ∈ T.dualRegionRim s ↔ r ∈ ({-1, 1} : Set ℝ)
  positive : ∀ s ∈ (T.marked 2).faces, s.card = 3 →
    ∀ p : (T.marked 2).vertices, (p : E) ∈ s → ∀ r ∈ I,
      0 ≤ T.height p (map s r) ↔ 0 ≤ r
  negative : ∀ s ∈ (T.marked 2).faces, s.card = 3 →
    ∀ p : (T.marked 2).vertices, (p : E) ∈ s → ∀ r ∈ I,
      T.height p (map s r) ≤ 0 ↔ r ≤ 0

theorem CoorientedSurfaceStars.exists_triangle_fibers
    (T : CoorientedSurfaceStars E) : Nonempty (SurfaceTriangleFibers T) := by
  classical
  let S := {s : Finset E // s ∈ (T.marked 2).faces ∧ s.card = 3}
  choose F hF hi him h0 hrim hpos hneg using
    fun s : S => T.exists_triangle_fiber s.property.1 s.property.2
  let f : Finset E → ℝ → E := fun s =>
    if h : s ∈ (T.marked 2).faces ∧ s.card = 3 then F ⟨s, h⟩ else fun _ => 0
  have hval (s : S) : f s = F s := by
    simp only [f, dif_pos s.property]
    rfl
  refine ⟨⟨f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hF ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hi ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact him ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact h0 ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hrim ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hpos ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hneg ⟨s, hs, hc⟩

end Geometry.SimplicialComplex
