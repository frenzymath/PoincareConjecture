import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Scalar.InterpolationCollar
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.BoundaryModulus
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Annulus.Reflection

/-!
# Two-sided area transport for free boundary lifts

The one-sided scalar collar is oriented from `c` to `c ∘ sigma`.  A reflected
copy has the reverse orientation.  Two exact annulus joins therefore transport
an arbitrary free-boundary candidate back to the fixed boundary class, provided
the two boundary curves have the explicit regularity required by the collar.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem m64PeriodicDegreeOneLift_continuous
    (sigma : M64PeriodicDegreeOneLift) : Continuous sigma.map := by
  have hLip : LipschitzWith
      (NNReal.mk sigma.lipschitz_constant sigma.lipschitz_nonnegative) sigma.map := by
    intro x y
    have hE := ENNReal.ofReal_le_ofReal (sigma.lipschitz_on x y)
    rw [ENNReal.ofReal_mul sigma.lipschitz_nonnegative] at hE
    simpa only [edist_dist, Real.dist_eq, ENNReal.coe_nnreal_eq, NNReal.coe_mk] using hE
  exact hLip.continuous

/-- Two actual zero-area collars transport every free-label annulus to the original literal
boundary class with exactly the same area. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449, and Lemma 19.31, pp. 464-466; project derivation
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
theorem m64FreeBoundaryAreaTransport_of_collars
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (hc0 : Continuous c0)
    (hc0_periodic : ∀ x : ℝ, c0 (x + curvePeriod) = c0 x)
    (hc0_lipschitz : ∃ Lc : ℝ, 0 ≤ Lc ∧ ∀ x y : ℝ,
      g.edist (c0 x) (c0 y) ≤ ENNReal.ofReal Lc * ENNReal.ofReal |x - y|)
    (hc1 : Continuous c1)
    (hc1_periodic : ∀ x : ℝ, c1 (x + curvePeriod) = c1 x)
    (hc1_lipschitz : ∃ Lc : ℝ, 0 ≤ Lc ∧ ∀ x y : ℝ,
      g.edist (c1 x) (c1 y) ≤ ENNReal.ofReal Lc * ENNReal.ofReal |x - y|) :
    M64FreeBoundaryAreaTransport g c0 c1 := by
  intro sigma0 sigma1 A
  have hsigma0 : Continuous sigma0.map := m64PeriodicDegreeOneLift_continuous sigma0
  have hsigma1 : Continuous sigma1.map := m64PeriodicDegreeOneLift_continuous sigma1
  have hsigma0_lipschitz : ∃ Ls : ℝ, 0 ≤ Ls ∧ ∀ x y : ℝ,
      |sigma0.map x - sigma0.map y| ≤ Ls * |x - y| := by
    exact ⟨sigma0.lipschitz_constant, sigma0.lipschitz_nonnegative,
      sigma0.lipschitz_on⟩
  have hsigma1_lipschitz : ∃ Ls : ℝ, 0 ≤ Ls ∧ ∀ x y : ℝ,
      |sigma1.map x - sigma1.map y| ≤ Ls * |x - y| := by
    exact ⟨sigma1.lipschitz_constant, sigma1.lipschitz_nonnegative,
      sigma1.lipschitz_on⟩
  obtain ⟨C0, hC0map, hC0area⟩ := m64_zero_area_boundary_collar g c0 sigma0.map
    hc0 hc0_periodic hc0_lipschitz hsigma0 sigma0.period_shift hsigma0_lipschitz
  obtain ⟨C1, hC1map, hC1area⟩ := m64_zero_area_boundary_collar g c1 sigma1.map
    hc1 hc1_periodic hc1_lipschitz hsigma1 sigma1.period_shift hsigma1_lipschitz
  obtain ⟨D, hDmap, hDarea⟩ := m64Annulus_join_with_area C0 A
  let C1reverse := m64Annulus_reverse C1
  obtain ⟨E, hEmap, hEarea⟩ := m64Annulus_join_with_area D C1reverse
  refine ⟨E, ?_⟩
  calc
    E.area = D.area + C1reverse.area := hEarea
    _ = (C0.area + A.area) + C1.area := by
      rw [m64Annulus_reverse_area, hDarea]
    _ = A.area := by rw [hC0area, hC1area]; ring

end PoincareMT
