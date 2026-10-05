import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckFrontierDistance

/-!
# Short retained-path segments stay in an axial slab

The cap-boundary crossing uses the sharp axial displacement estimate on a
segment that is already known to remain in one selected neck.  This is the
path form of the slab escape estimate; it does not turn an ambient distance
bound into a carrier path or assume a global completeness witness.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
/-- A retained path segment shorter than the sharp axial cost of a radius `r`
cannot leave the axial slab of radius `r` about its initial height. -/
theorem path_endpoint_mem_slab_of_short_length (W : EpsilonNeck g)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγW : MapsTo γ (Icc a b) W.carrier) {r : ℝ} (hr : 0 < r)
    (_hrA : r < W.epsilon⁻¹ -
      |(W.coordinate_inverse (γ a)).2|)
    (hshort : g.pathELength γ a b <
      ENNReal.ofReal ((W.scale * Real.sqrt (1 - W.epsilon)) * r)) :
    γ b ∈ W.region
      ((W.coordinate_inverse (γ a)).2 - r)
      ((W.coordinate_inverse (γ a)).2 + r) := by
  have hfactor : 0 < W.scale * Real.sqrt (1 - W.epsilon) := by
    exact mul_pos W.scale_pos
      (Real.sqrt_pos.mpr (by linarith [W.epsilon_lt_half]))
  have hdisp := W.path_axial_displacement_le_sharp hab hγ hγW
  have hcost : ENNReal.ofReal
      ((W.scale * Real.sqrt (1 - W.epsilon)) *
        |(W.coordinate_inverse (γ b)).2 -
          (W.coordinate_inverse (γ a)).2|) <
      ENNReal.ofReal ((W.scale * Real.sqrt (1 - W.epsilon)) * r) :=
    hdisp.trans_lt hshort
  have hreal : W.scale * Real.sqrt (1 - W.epsilon) *
      |(W.coordinate_inverse (γ b)).2 -
        (W.coordinate_inverse (γ a)).2| <
      W.scale * Real.sqrt (1 - W.epsilon) * r := by
    exact (ENNReal.ofReal_lt_ofReal_iff
      (mul_pos hfactor hr)).mp hcost
  have habs : |(W.coordinate_inverse (γ b)).2 -
      (W.coordinate_inverse (γ a)).2| < r := by
    nlinarith [hreal, hfactor]
  have habs' := (abs_lt.mp habs)
  refine ⟨hγW ⟨hab, le_rfl⟩, ?_, ?_⟩
  · linarith [habs'.1]
  · linarith [habs'.2]

end PoincareMT.M28
