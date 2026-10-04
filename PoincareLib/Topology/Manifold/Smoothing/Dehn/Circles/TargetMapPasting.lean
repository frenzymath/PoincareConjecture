import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polyhedra.Mathlib.PolyhedralPLClosedUnion
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolyhedralPLDiskExtension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLComposition
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLInverse

/-!
# Pasting the transported target formulas for circle attachment

The two formulas agree on the entire common carrier. Their finite
triangulations and compatible original target charts give a PL map
on the literal union, including every seam point. See Dehn022,
section 10, and Hatcher 2014, section 3.1, printed pp. 56--57.
-/

set_option autoImplicit false

open Set Geometry

namespace Dehn

/-- Paste two original-atlas PL formulas on their exact finite carriers.
This asserts no injectivity or local embedding at their common boundary. -/
theorem exists_circle_attachment_map_union
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    {f₀ f₁ : E → X} (h₀ : PolyhedralPLInCharts e f₀ K.space)
    (h₁ : PolyhedralPLInCharts e f₁ L.space)
    (hagree : ∀ x ∈ K.space, x ∈ L.space → f₀ x = f₁ x) :
    ∃ g : E → X, PolyhedralPLInCharts e g (K.space ∪ L.space) ∧
      EqOn g f₀ K.space ∧ EqOn g f₁ L.space := by
  classical
  let g : E → X := fun x => if x ∈ K.space then f₀ x else f₁ x
  have hg₀ : EqOn g f₀ K.space := fun x hx => if_pos hx
  have hg₁ : EqOn g f₁ L.space := by
    intro x hx
    by_cases hxK : x ∈ K.space
    · exact (hg₀ hxK).trans (hagree x hxK hx)
    · exact if_neg hxK
  refine ⟨g, ?_, hg₀, hg₁⟩
  exact PolyhedralPLInCharts.union_of_finite hcompat K L hK hL
    (h₀.congr (fun x hx => (hg₀ hx).symm))
    (h₁.congr (fun x hx => (hg₁ hx).symm))

end Dehn
