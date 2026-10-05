/-
Copyright (c) 2026 The PoincareLib contributors.
-/
import PoincareLib.Analysis.Calculus.Sard.OneDimensional
import PoincareLib.Topology.Surface.Triangulation.Edges

/-!
# Choosing levels with finite edge intersections

For any smooth scalar function on a surface, its restriction to finitely many
compact smooth arcs has simultaneous regular levels in every open interval.
The chosen level avoids all endpoints and meets each arc in finitely many
points. This supplies level choices for a general-position construction; it
does not construct a chart-face cover in general position.

Reference: Lee, *Introduction to Riemannian Manifolds*, second edition,
Problem 9-5, p. 281, as an alternative intersection-control step.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- A smooth function has levels meeting every edge of a prescribed finite
family in finitely many points, regularly and away from endpoints. -/
theorem exists_finite_smoothEdge_level_intersections {I : Type v} [Finite I]
    (e : I → SmoothEdge M) (g : M → ℝ)
    (hg : ContMDiff (𝓡 2) (𝓘(ℝ, ℝ)) ∞ g)
    (s : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, c ∉ s ∧ ∀ i,
      g ((e i).map 0) ≠ c ∧ g ((e i).map 1) ≠ c ∧
      ((e i).map '' Icc (0 : ℝ) 1 ∩ g ⁻¹' {c}).Finite ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, g ((e i).map t) = c →
        deriv (fun u => g ((e i).map u)) t ≠ 0 := by
  have hcomp (i : I) : ContDiffOn ℝ ∞ (fun t => g ((e i).map t)) (Icc (0 : ℝ) 1) :=
    (hg.comp_contMDiffOn (e i).smooth).contDiffOn
  obtain ⟨c, hc, havoid, hreg⟩ := Poincare.Analysis.exists_simultaneous_finite_regular_fibers
    (fun i t => g ((e i).map t)) (fun _ => 0) (fun _ => 1)
    (fun i => (hcomp i).continuousOn)
    (fun i => ((hcomp i).differentiableOn (by simp)).mono Ioo_subset_Icc_self) s hab
  refine ⟨c, hc, havoid, fun i => ⟨(hreg i).1, (hreg i).2.1, ?_, (hreg i).2.2.2⟩⟩
  apply ((hreg i).2.2.1.image (e i).map).subset
  rintro x ⟨⟨t, ht, rfl⟩, hx⟩
  exact ⟨t, ⟨ht, hx⟩, rfl⟩

end PoincareMT.Topology.Surface
