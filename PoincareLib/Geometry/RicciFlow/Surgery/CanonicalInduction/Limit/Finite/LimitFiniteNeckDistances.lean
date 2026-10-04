import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapPersistenceNormalization

/-!
# Explicit distances at the actual doubled neck accuracy

The intrinsic spherical competitor costs at most twenty scales. A
unit-speed segment from the literal center to a half-neck slice takes
at least twenty-five scales at epsilon <= 1/100.
MT Proposition 17.1; limit-finite-neck-exits.md, T1-T2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- The original intrinsic spherical competitor bounds actual distance
between any two carrier points at the same literal neck height. -/
theorem limitFinite_same_height_distance
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier)
    (hheight : (N.coordinate_inverse x).2 = (N.coordinate_inverse y).2) :
    (g.edist x y).toReal ≤ 20 * N.scale := by
  have hscale := N.scale_pos
  have hroot : Real.sqrt (1 + N.epsilon) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith [N.epsilon_lt_half]
  have hroot2 : Real.sqrt 2 ≤ 2 := by norm_num
  have hangle : Real.sqrt 2 * (Real.pi + 1) ≤ 10 := by
    calc
      _ ≤ 2 * 5 := mul_le_mul hroot2 (by linarith [Real.pi_le_four])
        (by positivity) (by norm_num)
      _ = 10 := by norm_num
  have hfactor : N.scale * Real.sqrt (1 + N.epsilon) *
      (Real.sqrt 2 * (Real.pi + 1)) ≤ 20 * N.scale := by
    calc
      _ ≤ (N.scale * 2) * 10 := mul_le_mul
        (mul_le_mul_of_nonneg_left hroot N.scale_pos.le) hangle
        (by positivity) (by positivity)
      _ = _ := by ring
  have hlength := (edist_le_intrinsicEDist (g := g) N.carrier x y).trans
    (N.intrinsicEDist_le_axial_add hx hy)
  simp only [hheight, sub_self, abs_zero, zero_add] at hlength
  have hbound := hlength.trans (ENNReal.ofReal_le_ofReal hfactor)
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 20 * N.scale)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

/-- The actual center has axial coordinate zero, so a unit-speed
half-neck hit occurs no earlier than twenty-five scales. -/
theorem limitFinite_half_neck_time_lower
    (hepsilon : N.epsilon ≤ 1 / 100) {gamma : ℝ → M} {s : ℝ} (hs : 0 ≤ s)
    (hgamma : g.IsGeodesicOn gamma (Icc 0 s))
    (hcarrier : MapsTo gamma (Icc 0 s) N.carrier)
    (hspeed : ∀ t ∈ Icc 0 s,
      g.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1) = 1)
    (hstart : gamma 0 = N.center)
    (hboundary : |(N.coordinate_inverse (gamma s)).2| = N.epsilon⁻¹ / 2) :
    25 * N.scale ≤ s := by
  have heps := N.epsilon_pos
  have haxis0 := ((N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere).2
  have hdisp := N.axial_displacement_le_of_unit_speed hs hgamma hcarrier hspeed
  rw [hstart, haxis0, sub_zero, hboundary] at hdisp
  have hroot : 1 / 2 ≤ Real.sqrt (1 - N.epsilon) := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith))
  have hscaled := (le_inv_mul_iff₀ hfactor).mp hdisp
  have hlow := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hroot N.scale_pos.le)
    (by positivity : 0 ≤ N.epsilon⁻¹ / 2)).trans hscaled
  have hinv : 100 ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith
  have hproduct := mul_le_mul_of_nonneg_left hinv N.scale_pos.le
  nlinarith

end PoincareMT.M47
