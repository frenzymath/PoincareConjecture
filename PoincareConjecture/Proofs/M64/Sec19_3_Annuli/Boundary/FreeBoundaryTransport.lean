import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ScalarInterpolationCollar
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.AnnulusReflection













set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

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

end PoincareConjecture
