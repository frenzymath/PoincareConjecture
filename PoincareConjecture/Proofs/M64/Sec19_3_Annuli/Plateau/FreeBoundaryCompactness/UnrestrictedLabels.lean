import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FreeBoundaryTransport













set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M64



structure LipschitzDegreeOneLabel where
  map : ℝ → ℝ
  period_shift : ∀ x, map (x + curvePeriod) = map x + curvePeriod
  constant : ℝ≥0
  lipschitz : LipschitzWith constant map



def LipschitzDegreeOneLabel.ofMonotone (sigma : M64PeriodicDegreeOneLift) :
    LipschitzDegreeOneLabel where
  map := sigma.map
  period_shift := sigma.period_shift
  constant := ⟨sigma.lipschitz_constant, sigma.lipschitz_nonnegative⟩
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |sigma.map x - sigma.map y| ≤ sigma.lipschitz_constant * |x - y|
    exact sigma.lipschitz_on x y




theorem LipschitzDegreeOneLabel.scalar_bound (sigma : LipschitzDegreeOneLabel) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |sigma.map x - sigma.map y| ≤ L * |x - y| := by
  refine ⟨sigma.constant, sigma.constant.coe_nonneg, ?_⟩
  intro x y
  simpa only [Real.dist_eq] using sigma.lipschitz.dist_le_mul x y




def LipschitzDegreeOneLabel.addPeriodic (sigma : LipschitzDegreeOneLabel)
    (theta : ℝ → ℝ) (htheta : Function.Periodic theta curvePeriod)
    {K : ℝ≥0} (hK : LipschitzWith K theta) (t : ℝ) : LipschitzDegreeOneLabel where
  map x := sigma.map x + t * theta x
  period_shift x := by rw [sigma.period_shift, htheta x]; ring
  constant := sigma.constant + ‖t‖₊ * K
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hs := sigma.lipschitz.dist_le_mul x y
    have ht := hK.dist_le_mul x y
    simp only [Real.dist_eq] at hs ht ⊢
    have htri := abs_add_le (sigma.map x - sigma.map y) (t * (theta x - theta y))
    calc
      |sigma.map x + t * theta x - (sigma.map y + t * theta y)| =
          |(sigma.map x - sigma.map y) + t * (theta x - theta y)| := by congr 1; ring
      _ ≤ |sigma.map x - sigma.map y| + |t * (theta x - theta y)| := htri
      _ ≤ (sigma.constant : ℝ) * |x - y| + |t| * ((K : ℝ) * |x - y|) := by
        rw [abs_mul]
        exact add_le_add hs (mul_le_mul_of_nonneg_left ht (abs_nonneg t))
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]; ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem unrestricted_label_area_transport
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (hc0 : Continuous c0) (hp0 : Function.Periodic c0 curvePeriod)
    (hL0 : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
      g.edist (c0 x) (c0 y) ≤ ENNReal.ofReal L * ENNReal.ofReal |x - y|)
    (hc1 : Continuous c1) (hp1 : Function.Periodic c1 curvePeriod)
    (hL1 : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
      g.edist (c1 x) (c1 y) ≤ ENNReal.ofReal L * ENNReal.ofReal |x - y|)
    (sigma0 sigma1 : LipschitzDegreeOneLabel)
    (A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map)) :
    ∃ B : M64Annulus g c0 c1, B.area = A.area := by
  obtain ⟨C0, -, hC0⟩ := m64_zero_area_boundary_collar g c0 sigma0.map hc0 hp0 hL0
    sigma0.lipschitz.continuous sigma0.period_shift sigma0.scalar_bound
  obtain ⟨C1, -, hC1⟩ := m64_zero_area_boundary_collar g c1 sigma1.map hc1 hp1 hL1
    sigma1.lipschitz.continuous sigma1.period_shift sigma1.scalar_bound
  obtain ⟨D, -, hD⟩ := m64Annulus_join_with_area C0 A
  obtain ⟨B, -, hB⟩ := m64Annulus_join_with_area D (m64Annulus_reverse C1)
  refine ⟨B, ?_⟩
  rw [hB, m64Annulus_reverse_area, hD, hC0, hC1]
  ring

end PoincareConjecture.M64
