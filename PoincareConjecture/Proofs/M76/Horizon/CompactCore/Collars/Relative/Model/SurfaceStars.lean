import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.HalfPlaneIncidence
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

local notation "C3" => ((ℝ × ℝ) × ℝ)

structure CoorientedSurfaceStars where
  ambient : SimplicialComplex ℝ E
  marked : Fin 4 → SimplicialComplex ℝ E
  finite : ambient.faces.Finite
  marked_le : ∀ i, marked i ≤ ambient
  marked_full : ∀ i s, s ∈ ambient.faces →
    (∀ v ∈ s, v ∈ (marked i).vertices) → s ∈ (marked i).faces
  boundary_subset_region : (marked 1).space ⊆ (marked 0).space
  surface_subset_region : (marked 2).space ⊆ (marked 0).space
  surface_boundary_inter : (marked 2).space ∩ (marked 1).space = (marked 3).space
  chart : (marked 2).vertices → E → C3
  star_affine : ∀ p : (marked 2).vertices, (ambient.closedStar p).AffineOnFaces (chart p)
  star_injective : ∀ p : (marked 2).vertices, InjOn (chart p) (ambient.closedStar p).space
  star_interior : ∀ p : (marked 2).vertices,
    chart p p ∈ interior (chart p '' (ambient.closedStar p).space)
  chart_model : ∀ p : (marked 2).vertices,
    ((ambient.closedStar p).space ⊆ (marked 0).space ∧
      Disjoint (ambient.closedStar p).space (marked 1).space) ∨
    ((∀ x ∈ (ambient.closedStar p).space,
        x ∈ (marked 0).space ↔ 0 ≤ (chart p x).1.1) ∧
      ∀ x ∈ (ambient.closedStar p).space,
        x ∈ (marked 1).space ↔ (chart p x).1.1 = 0)
  surface_eq : ∀ (p : (marked 2).vertices) x, x ∈ (ambient.closedStar p).space →
    (x ∈ (marked 2).space ↔ x ∈ (marked 0).space ∧ (chart p x).2 = 0)
  nonneg_agree : ∀ (p q : (marked 2).vertices) x, x ∈ (ambient.closedStar p).space →
    x ∈ (ambient.closedStar q).space →
    (0 ≤ (chart p x).2 ↔ 0 ≤ (chart q x).2)
  zero_agree : ∀ (p q : (marked 2).vertices) x, x ∈ (ambient.closedStar p).space →
    x ∈ (ambient.closedStar q).space →
    ((chart p x).2 = 0 ↔ (chart q x).2 = 0)

namespace CoorientedSurfaceStars

variable {E} (T : CoorientedSurfaceStars E)

theorem marked_finite (i : Fin 4) : (T.marked i).faces.Finite :=
  T.finite.subset (T.marked_le i)

theorem star_subset_ambient (p : (T.marked 2).vertices) :
    (T.ambient.closedStar p).space ⊆ T.ambient.space :=
  space_subset_of_le (fun _ hs => hs.1)

theorem nonpos_agree (p q : (T.marked 2).vertices) {x : E}
    (hp : x ∈ (T.ambient.closedStar p).space)
    (hq : x ∈ (T.ambient.closedStar q).space) :
    (T.chart p x).2 ≤ 0 ↔ (T.chart q x).2 ≤ 0 := by
  have hpos := T.nonneg_agree p q x hp hq
  have hz := T.zero_agree p q x hp hq
  constructor <;> intro h
  · by_cases he : (T.chart p x).2 = 0
    · exact (hz.mp he).le
    · have hn : ¬ 0 ≤ (T.chart p x).2 := fun hh => he (le_antisymm h hh)
      exact (lt_of_not_ge (fun hh => hn (hpos.mpr hh))).le
  · by_cases he : (T.chart q x).2 = 0
    · exact (hz.mpr he).le
    · have hn : ¬ 0 ≤ (T.chart q x).2 := fun hh => he (le_antisymm h hh)
      exact (lt_of_not_ge (fun hh => hn (hpos.mp hh))).le

end CoorientedSurfaceStars
end Geometry.SimplicialComplex
