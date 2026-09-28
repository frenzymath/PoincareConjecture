import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClosedC1MetricLipschitz
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicRectangleAdmission

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64Annulus_exists_eqOn_rectangle_of_contMDiffOn
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (hc0 : Function.Periodic c0 curvePeriod) (hc1 : Function.Periodic c1 curvePeriod)
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      f (annulusPoint curvePeriod s) = f (annulusPoint 0 s))
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod, f (annulusPoint x 1) = c1 x) :
    ∃ A : M64Annulus g c0 c1, EqOn A.map f m64AnnulusDomain := by
  obtain ⟨K, hK⟩ := m64Annulus_hLip_of_contMDiffOn g hf
  apply m64Annulus_exists_eqOn_rectangle_of_lipschitz g hc0 hc1 f hf.continuousOn
    hseam hlower hupper K.coe_nonneg
  intro x y
  simpa only [ENNReal.ofReal_coe_nnreal] using hK x y

end PoincareConjecture
