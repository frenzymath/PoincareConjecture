import PoincareLib.Geometry.Riemannian.Soul.Point.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Propagation across a connected soul exterior

The radial homeomorphism makes every exterior of a closed soul ball
connected. A locally propagating nonempty set, with an open reverse
incidence relation, fills that exterior. This supplies a connectedness
form of the first-failure argument in Morgan--Tian, Proposition 9.85(1),
pp. 237--239.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.CoreRadius

/-- Local propagation in both variables makes the propagated set clopen. -/
theorem eq_univ_of_open_propagation
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (G : Set X) (hG : G.Nonempty) (O : X → X → Prop)
    (hrow : ∀ x, IsOpen {y | O x y}) (hcolumn : ∀ y, IsOpen {x | O x y})
    (hrefl : ∀ x, O x x)
    (hprop : ∀ x ∈ G, ∀ y, O x y → y ∈ G) : G = univ := by
  have hopen : IsOpen G := isOpen_iff_mem_nhds.mpr fun x hx =>
    Filter.mem_of_superset ((hrow x).mem_nhds (hrefl x)) (fun y hy => hprop x hx y hy)
  have hclosed : IsClosed G := isClosed_of_closure_subset fun y hy => by
    obtain ⟨x, hxy, hx⟩ := mem_closure_iff.mp hy {x | O x y} (hcolumn y) (hrefl y)
    exact hprop x hx y hxy
  exact IsClopen.eq_univ ⟨hclosed, hopen⟩ hG

end PoincareMT.CoreRadius

namespace PoincareMT.RiemannianMetric.PointSoulData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- Every exterior of a closed soul ball is connected in the actual metric. -/
theorem isPreconnected_exterior (S : PointSoulData g) {D : ℝ} (hD : 0 ≤ D) :
    IsPreconnected {x : M | D < (g.edist S.center x).toReal} := by
  let : PreconnectedSpace UnitTwoSphere := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (by simp [← Module.finrank_eq_rank])
      (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let : PreconnectedSpace (Ioi D) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioi
  let j : Ioi D → Ioi (0 : ℝ) := fun r => ⟨r.val, hD.trans_lt r.property⟩
  let f : UnitTwoSphere × Ioi D → M := fun z =>
    (S.radial.toHomeomorph (z.1, j z.2)).val
  have hf : Continuous f := continuous_subtype_val.comp
    (S.radial.toHomeomorph.continuous.comp
      (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))
  have heq : range f = {x : M | D < (g.edist S.center x).toReal} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      change D < (g.edist S.center (S.radial.toHomeomorph (z.1, j z.2)).val).toReal
      rw [S.radial.distance_eq]
      exact z.2.property
    · intro hx
      change D < (g.edist S.center x).toReal at hx
      have hne : x ≠ S.center := by
        rintro rfl
        simp only [RiemannianMetric.edist,
          Manifold.riemannianEDist_self, ENNReal.toReal_zero] at hx
        exact (not_lt_of_ge hD) hx
      let z := S.radial.toHomeomorph.symm ⟨x, hne⟩
      have hz : D < z.2.val := by
        rw [← S.radial.distance_eq z]
        simpa only [z, S.radial.toHomeomorph.apply_symm_apply] using hx
      refine ⟨(z.1, ⟨z.2.val, hz⟩), ?_⟩
      change (S.radial.toHomeomorph z).val = x
      exact congrArg Subtype.val (S.radial.toHomeomorph.apply_symm_apply ⟨x, hne⟩)
  rw [← heq]
  exact isPreconnected_range hf

end PoincareMT.RiemannianMetric.PointSoulData
