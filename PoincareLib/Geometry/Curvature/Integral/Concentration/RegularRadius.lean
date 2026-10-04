import PoincareLib.Geometry.Alexandrov.Packing.PuncturedAscent
import PoincareLib.Geometry.Curvature.Integral.Concentration.PuncturedCover

/-!
# Regular radii and finite punctured covers

Comparison-angle packing and the Alexandrov curvature bound construct a
positive radius function with near-unit local distance ascent. Compactness
then leaves only finitely many points outside its punctured balls.

Reference: Petrunin (2009), Sections 3.3--3.5, author manuscript p. 6,
and Section 4.6, pp. 12--13.
-/

noncomputable section
set_option autoImplicit false

open Set Poincare.Alexandrov

namespace Poincare.CurvatureIntegral

/-- The metric geometry constructs positive capped radii on whose doubled
punctured balls the distance from the center has strict local ascent. -/
theorem exists_regular_radius_function
    {X : Type*} [MetricSpace X]
    (hX : CurvatureGEnegOne X)
    (hgeo : ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hpacking : ∀ α : ℝ, 0 < α → ∃ N : ℕ, ComparisonAnglePackingBound X α N)
    {c R : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hR : 0 < R) :
    ∃ b : X → ℝ, (∀ p, 0 < b p ∧ 2 * b p ≤ R) ∧
      ∀ p y : X, 0 < dist p y → dist p y < 2 * b p →
        ∀ s : ℝ, 0 < s → ∃ z : X,
          dist y z < s ∧ c * dist y z < dist p z - dist p y := by
  classical
  choose r hr hascent using
    exists_pos_punctured_distance_ascent hX hgeo hpacking hc0 hc1
  refine ⟨fun p => min (r p) R / 2, ?_, ?_⟩
  · intro p
    constructor
    · exact half_pos (lt_min (hr p) hR)
    · linarith [min_le_right (r p) R]
  · intro p y hpy hy
    apply hascent p y hpy
    linarith [min_le_left (r p) R]

/-- Actual regular radii give a finite punctured cover of a compact set
outside precisely its finite set of spires. -/
theorem exists_regular_radius_finite_punctured_cover
    {X : Type*} [MetricSpace X]
    (hX : CurvatureGEnegOne X)
    (hgeo : ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y)
    (hpacking : ∀ α : ℝ, 0 < α → ∃ N : ℕ, ComparisonAnglePackingBound X α N)
    {c R : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hR : 0 < R)
    {K : Set X} (hK : IsCompact K) :
    ∃ b : X → ℝ, ∃ F S : Finset X,
      (∀ p, 0 < b p ∧ 2 * b p ≤ R) ∧
      (∀ p y : X, 0 < dist p y → dist p y < 2 * b p →
        ∀ s : ℝ, 0 < s → ∃ z : X,
          dist y z < s ∧ c * dist y z < dist p z - dist p y) ∧
      (S : Set X) = {x | x ∈ K ∧ ∀ y, y ≠ x → b y ≤ dist y x} ∧
      K \ (S : Set X) ⊆ ⋃ y ∈ F, Metric.ball y (b y) \ {y} := by
  obtain ⟨b, hb, hascent⟩ := exists_regular_radius_function hX hgeo hpacking hc0 hc1 hR
  obtain ⟨F, S, hS, hcover⟩ := exists_finite_punctured_ball_cover hK b (fun p => (hb p).1)
  exact ⟨b, F, S, hb, hascent, hS, hcover⟩

end Poincare.CurvatureIntegral
