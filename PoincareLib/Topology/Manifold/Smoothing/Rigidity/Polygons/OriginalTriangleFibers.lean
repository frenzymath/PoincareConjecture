import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polygons.OriginalTriangleFiber

/-!
# The once-chosen family of original triangle fibers

Each actual fiber is produced from the retained original model before
any incident edge is extended. No geometric supplier is added.
See Hudson1969, pp.58--63 and rigidity025, section3.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

/-- The actual complete triangle fibers retained once for every
later incident edge. Existence below constructs them from T alone.
See rigidity025, section3. -/
structure OriginalTriangleFibers (T : OriginalProperDiskTriangulation e R j) where
  map : Finset (T.index → ℝ × V3) → ℝ → (T.index → ℝ × V3)
  piecewiseAffine : ∀ s ∈ (T.marked 2).faces, s.card = 3 →
    FinitePiecewiseAffineOn (map s) I
  injective : ∀ s ∈ (T.marked 2).faces, s.card = 3 → InjOn (map s) I
  image_eq : ∀ s ∈ (T.marked 2).faces, s.card = 3 → map s '' I = T.dualRegion s
  central : ∀ s ∈ (T.marked 2).faces, s.card = 3 → map s 0 = s.centroid ℝ id
  rim : ∀ s ∈ (T.marked 2).faces, s.card = 3 → ∀ r ∈ I,
    map s r ∈ T.dualRegionRim s ↔ r ∈ ({-1, 1} : Set ℝ)
  positive : ∀ s ∈ (T.marked 2).faces, s.card = 3 →
    ∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s → ∀ r ∈ I,
      0 ≤ T.height p (map s r) ↔ 0 ≤ r
  negative : ∀ s ∈ (T.marked 2).faces, s.card = 3 →
    ∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s → ∀ r ∈ I,
      T.height p (map s r) ≤ 0 ↔ r ≤ 0

/-- The original geometry constructs the whole retained triangle
fiber family. No fiber, side or interval premise occurs.
See rigidity025, section3. -/
theorem OriginalProperDiskTriangulation.exists_triangle_fibers [T2Space X]
    (T : OriginalProperDiskTriangulation e R j) : Nonempty (OriginalTriangleFibers T) := by
  classical
  let S := {s : Finset (T.index → ℝ × V3) // s ∈ (T.marked 2).faces ∧ s.card = 3}
  choose F hF hi him h0 hrim hpos hneg using
    fun s : S => T.exists_triangle_fiber s.property.1 s.property.2
  let f : Finset (T.index → ℝ × V3) → ℝ → (T.index → ℝ × V3) := fun s =>
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

end PoincareMT.M76
