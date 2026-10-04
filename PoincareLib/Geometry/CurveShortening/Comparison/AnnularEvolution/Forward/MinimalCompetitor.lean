import PoincareLib.Geometry.CurveShortening.Comparison.AnnulusTheory
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Infimum

/-!
# Forward difference from minimal-annulus competitors

The first-variation producer supplies an admissible annulus at time `t + h`
whose area is bounded by the attained minimum at time `t` plus an `O(h)`
error.  This file performs only the guarded infimum reduction; existence,
regularity, and the first-variation estimate remain explicit producer inputs.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

/-- Actual future competitors above an attained infimum imply the stated positive-increment
upper forward bound. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
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

end PoincareMT
