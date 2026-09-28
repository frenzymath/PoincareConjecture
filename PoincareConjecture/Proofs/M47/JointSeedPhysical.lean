import PoincareConjecture.Proofs.M47.JointSeedWorldline
import PoincareConjecture.Proofs.M47.ComponentEstimateCanonical











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47



theorem jointSeed_physical_low_point_gap
    (P : M47ScalarPersistencePredecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] {J : Set ℝ} (G : RicciFlow 3 M J)
    (F : SurgeryFlowData.{u}) {s t C L : ℝ} (q : M)
    (phi : M → (F.slice s).carrier)
    (himage : ∀ p : M, phi p ∈ connectedComponent (phi q))
    (hread : ∀ p : M, (G.connection s).scalarCurvature p =
      (F.connection s).scalarCurvature (phi p))
    (hst : s ≤ t) (hJ : Icc s t ⊆ J) (hC : 1 ≤ C)
    (hscalar : ∀ p : M, 0 ≤ (G.connection s).scalarCurvature p)
    (hterminal : C * (G.connection t).scalarCurvature q ≤ L)
    (hhigh : L < (G.connection s).scalarCurvature q) :
    ∃ p ∈ connectedComponent (phi q),
      (C / 6) * (F.connection s).scalarCurvature p ≤
        (F.connection s).scalarCurvature (phi q) := by
  obtain ⟨p, hp⟩ := jointSeed_compact_low_point_gap P G q hst hJ hC hscalar hterminal hhigh
  refine ⟨phi p, himage p, ?_⟩
  simpa only [hread] using hp




theorem exists_jointSeed_physical_analytic_bound (C : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ C ≤ A ∧
      ∀ (F : SurgeryFlowData.{u}) (s : ℝ) (p q : (F.slice s).carrier),
        p ∈ connectedComponent q →
        (C / 6) * (F.connection s).scalarCurvature p ≤
          (F.connection s).scalarCurvature q →
        SurgeryCanonicalControl F s q F.parameters.epsilon C →
        M45PointwiseAnalyticEstimate (F.metric s) (F.connection s) q A := by
  obtain ⟨B, _hB, hmodel⟩ := exists_component_crossing_analytic_bound.{u} C
  let A := max 1 (max C B)
  have hBA : B ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro F s p q hp hgap hcanonical
  have h := hmodel F s q p q hp mem_connectedComponent hgap hcanonical
  exact ⟨h.1,
    h.2.1.trans (mul_le_mul_of_nonneg_right hBA (Real.rpow_nonneg h.1.le _)),
    h.2.2.trans (mul_le_mul_of_nonneg_right hBA (sq_nonneg _))⟩

end PoincareConjecture.M47
