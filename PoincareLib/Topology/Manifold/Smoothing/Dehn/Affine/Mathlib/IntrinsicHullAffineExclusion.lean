import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.IntrinsicFaceSaturation
import Mathlib.Analysis.Convex.Join

/-!
# The relative interior avoids the opposite affine span

Move an intrinsic-interior point a short distance away from the
distinguished vertex. The convex-join formula then forces that
vertex into the alleged opposite affine span, a contradiction.
This is the positive-coordinate step of Hudson1969, Lemma4.5,
used in Dehn029, section4.
-/

set_option autoImplicit false

open Set

namespace AffineSubspace

/-- When all generators except one lie in an affine subspace,
the intrinsic interior of their convex hull avoids that subspace
if the remaining generator does. See Dehn029, section4. -/
theorem disjoint_intrinsicInterior_convexHull_of_insert
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : AffineSubspace ℝ E) {s : Set E} {v : E}
    (hv : v ∈ s) (hsv : s ⊆ insert v (A : Set E)) (hvA : v ∉ A) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ s)) (A : Set E) := by
  apply Set.disjoint_left.mpr
  intro x hx hxA
  have hxC := intrinsicInterior_subset hx
  have hvC := subset_convexHull ℝ s hv
  have hd : x - v ∈ (affineSpan ℝ (convexHull ℝ s)).direction :=
    (affineSpan ℝ _).vsub_mem_direction (subset_affineSpan ℝ _ hxC)
      (subset_affineSpan ℝ _ hvC)
  obtain ⟨r, hr, hz⟩ := Set.exists_pos_smul_add_mem_of_intrinsicInterior hx hd
  have hz' := convexHull_mono hsv hz
  rw [convexHull_insert ⟨x, hxA⟩, A.convex.convexHull_eq] at hz'
  obtain ⟨u, hu, y, hy, hzseg⟩ := mem_convexJoin.mp hz'
  have hu' : u = v := hu
  subst u
  obtain ⟨a, b, ha, _, hab, he⟩ := hzseg
  have heq : (a + r) • (v - x) = (-b) • (y - x) := by
    calc
      (a + r) • (v - x) =
          (a • v + b • y) - (r • (x - v) + x) - b • (y - x) +
            (1 - a - b) • x := by module
      _ = (-b) • (y - x) := by
        rw [he, sub_self, show 1 - a - b = 0 by linarith]
        simp only [zero_sub, zero_smul, add_zero, neg_smul]
  have hdir : (a + r) • (v - x) ∈ A.direction := by
    rw [heq]
    exact A.direction.smul_mem _ (A.vsub_mem_direction hy hxA)
  have hne : a + r ≠ 0 := (add_pos_of_nonneg_of_pos ha hr).ne'
  have hvdir : v - x ∈ A.direction := (A.direction.smul_mem_iff hne).mp hdir
  apply hvA
  simpa only [vsub_eq_sub, vadd_eq_add, sub_add_cancel] using
    A.vadd_mem_of_mem_direction hvdir hxA

/-- Excluding one generator from the affine span of all other
source and target generators makes the full source relative
interior disjoint from the target convex hull. See Dehn029,
section4. No independence of the whole union is assumed. -/
theorem disjoint_intrinsicInterior_convexHulls_of_excluded_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set E} {v : E} (hv : v ∈ s)
    (hvA : v ∉ affineSpan ℝ ((s \ {v}) ∪ t)) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ s)) (convexHull ℝ t) := by
  let A := affineSpan ℝ ((s \ {v}) ∪ t)
  have hs : s ⊆ insert v (A : Set E) := by
    intro x hx
    by_cases he : x = v
    · exact Or.inl he
    · exact Or.inr (subset_affineSpan ℝ _ (Or.inl ⟨hx, he⟩))
  have hdis := A.disjoint_intrinsicInterior_convexHull_of_insert hv hs hvA
  apply hdis.mono_right
  exact convexHull_min (fun _ hx => subset_affineSpan ℝ _ (Or.inr hx)) A.convex

end AffineSubspace
