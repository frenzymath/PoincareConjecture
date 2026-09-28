import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionConstructor
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionIntegrability

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

theorem m64ProjectedAnnulus_of_annulus
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (t : ℝ) (c0 c1 : ℝ → P.charts.Point)
    (A : M64Annulus (P.flow.metric t) c0 c1) :
    0 ≤ A.area ∧
      ∃ B : M64Annulus (F.metric t) (fun x => (c0 x).1) (fun x => (c1 x).1),
        B.map = (fun z => (A.map z).1) ∧
        B.area = m64ProjectedAnnulusArea P t A ∧
        0 ≤ B.area ∧ B.area ≤ A.area := by
  exact m64ProjectedAnnulus_of_integrable P t c0 c1 A
    (m64ProjectedDensity_integrable P t c0 c1 A)

end PoincareConjecture
