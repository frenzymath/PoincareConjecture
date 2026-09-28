import PoincareConjecture.Proofs.M76.PrimeReduction.ConvexZeroSectionDisk
import PoincareConjecture.Proofs.M76.Triangulation.AffineConvexSphereCapDisks

set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem isFinitePLBallPair_convex_half_body_sides
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hC0 : (0 : E) ∈ interior C) (hspace : K.space = C)
    (A : E →ₗ[ℝ] ℝ) (v : E) (hv : A v = 1)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) :
    IsFinitePLBallPair F (frontier C ∩ {x | 0 ≤ A x})
        (frontier C ∩ {x | A x = 0}) ∧
      IsFinitePLBallPair F (C ∩ {x | A x = 0})
        (frontier C ∩ {x | A x = 0}) := by
  have hA : A ≠ 0 := by
    intro h
    simp [h] at hv
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hC0
  let r := ε / (‖v‖ + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  have hrv : r * ‖v‖ < ε := by
    change ε / (‖v‖ + 1) * ‖v‖ < ε
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have hq : -r • v ∈ interior C := by
    apply hball
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos hr]
    exact hrv
  have hqA : A (-r • v) < 0 := by
    rw [map_smul, hv, smul_eq_mul, mul_one]
    exact neg_lt_zero.mpr hr
  exact ⟨K.isFinitePLBallPair_convex_frontier_affine_cap hK hC hcv hspace
    A.toAffineMap ⟨-r • v, hq, hqA⟩ ⟨0, hC0, map_zero A⟩ hdim,
    K.isFinitePLBallPair_convex_zero_section hK hC hcv hspace A.toAffineMap
      hA ⟨0, hC0, map_zero A⟩ hdim⟩

end Geometry.SimplicialComplex
