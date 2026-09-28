import PoincareConjecture.Statements.M64Annulus
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

theorem m64AnnulusForward_of_minimal_competitors
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point} {t rate : ℝ}
    (A : M64Annulus (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hmin : A.area = m64FlowAnnulusArea P c0 c1 t)
    (hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area + h * (rate + eta)) :
    AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1) rate t := by
  intro eta heta
  filter_upwards [hcomp eta heta, self_mem_nhdsWithin] with h hB hh
  obtain ⟨B, hB⟩ := hB
  have hleast := m64LeastAnnulusArea_le_annulus B
  have hquot :
      (m64FlowAnnulusArea P c0 c1 (t + h) -
        m64FlowAnnulusArea P c0 c1 t) / h ≤ rate + eta := by
    have hleast' : m64FlowAnnulusArea P c0 c1 (t + h) ≤ B.area := by
      exact hleast
    rw [hmin] at hB
    dsimp only [m64FlowAnnulusArea] at hleast' hB ⊢
    rw [div_le_iff₀ hh]
    linarith
  exact hquot

end PoincareConjecture
