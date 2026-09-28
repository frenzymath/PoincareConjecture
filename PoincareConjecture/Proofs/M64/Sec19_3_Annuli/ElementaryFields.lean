import PoincareConjecture.Statements.M64Annulus
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}





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

end PoincareConjecture
