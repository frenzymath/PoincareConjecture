import PoincareLib.Geometry.CurveShortening.Comparison.AnnulusTheory
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Infimum

/-!
# Elementary fields of annular evolution

Once an admissible annulus is supplied at every time, the first three fields
of `M64AnnulusFlowConclusion` follow from the guarded area-range lemmas.  The
regularity, forward-variation, and exponential fields are deliberately left
to their geometric producers.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

/-- Actual annuli at each time supply nonempty area classes, lower bounds and nonnegative
least areas. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449;
project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusFlow_elementary_fields
    {circumference : ℝ} {P : M62.CircleProductData F circumference}
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hA : ∀ t ∈ Set.Icc a b,
      Nonempty (M64Annulus (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) :
    (∀ t ∈ Set.Icc a b,
      Nonempty (M64Annulus (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      BddBelow (m64AnnulusAreaRange (P.flow.metric t)
        (fun x => c0 x t) (fun x => c1 x t))) ∧
    (∀ t ∈ Set.Icc a b,
      0 ≤ m64FlowAnnulusArea P c0 c1 t) := by
  refine ⟨hA, ?_, ?_⟩
  · intro t ht
    exact m64AnnulusAreaRange_bddBelow (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t)
  · intro t ht
    obtain ⟨A⟩ := hA t ht
    simpa only [m64FlowAnnulusArea] using m64LeastAnnulusArea_nonneg A

end PoincareMT
