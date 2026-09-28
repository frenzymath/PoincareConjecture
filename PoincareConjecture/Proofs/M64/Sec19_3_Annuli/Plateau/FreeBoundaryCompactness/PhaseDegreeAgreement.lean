import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseGreenAdmission

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem annulus_boundary_phase_increment_eq
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map (interior m64AnnulusDomain))
    (L0 L1 : ℝ → ℝ) (hL0 : Continuous L0) (hL1 : Continuous L1)
    (hzero : ∀ x ∈ Icc (0 : ℝ) curvePeriod, P.circle.quotient (L0 x) = (c0 x).2)
    (hone : ∀ x ∈ Icc (0 : ℝ) curvePeriod, P.circle.quotient (L1 x) = (c1 x).2)
    {D0 D1 : ℝ} (hdegree0 : L0 curvePeriod = L0 0 + D0)
    (hdegree1 : L1 curvePeriod = L1 0 + D1) : D0 = D1 := by
  obtain ⟨L, k, -, -, -, -, -, -, hupper, hseam, -, -⟩ :=
    annulus_exists_real_weak_phase P t A hA L0 L1 hL0 hL1 hzero hone hdegree0
  have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hh := hseam 1 ⟨zero_le_one, le_rfl⟩
  rw [hupper curvePeriod ⟨hP, le_rfl⟩, hupper 0 ⟨le_rfl, hP⟩] at hh
  linarith

end PoincareConjecture.M64
