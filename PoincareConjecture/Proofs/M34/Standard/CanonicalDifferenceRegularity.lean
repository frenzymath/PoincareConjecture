import PoincareConjecture.Proofs.M34.Standard.CanonicalFlowRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem canonicalDomain_contDiffOn_difference_coordinates
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
      (R R' : ℝ → U → FS n),
      (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
      (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
      ∀ p : U,
        let r := (extChartAt (𝓡 n) p).symm
        let H : ℝ × V n → FH n := fun z =>
          (F.metric z.1).inner (r z.2) - (F'.metric z.1).inner (r z.2)
        let A : ℝ × V n → FA n := fun z => CovariantDerivative.difference
          (F.connection z.1).connection (F'.connection z.1).connection (r z.2)
        let S := fun z : ℝ × V n => R z.1 (r z.2) - R' z.1 (r z.2)
        ContDiffOn ℝ ∞ (fun z => qH (H z)) ((J ∩ J') ×ˢ U) ∧
        ContDiffOn ℝ ∞ (fun z => qA (A z)) ((J ∩ J') ×ˢ U) ∧
        ContDiffOn ℝ ∞ (fun z => qS (S z)) ((J ∩ J') ×ˢ U) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' R R' hR hR' p r H A S
  have hH : ContDiffOn (F := FH n) ℝ ∞ H ((J ∩ J') ×ˢ U) :=
    ((canonicalDomain_contDiffOn_flow_metric U hU qH F p).mono
      (Set.prod_mono inter_subset_left subset_rfl)).sub
      ((canonicalDomain_contDiffOn_flow_metric U hU qH F' p).mono
        (Set.prod_mono inter_subset_right subset_rfl))
  have hA : ContDiffOn (F := FA n) ℝ ∞ A ((J ∩ J') ×ˢ U) :=
    canonicalDomain_contDiffOn_connection_difference U hU qA F F' p
  have hS : ContDiffOn (F := FS n) ℝ ∞ S ((J ∩ J') ×ˢ U) :=
    ((canonicalDomain_contDiffOn_flow_curvature U hU qS F R hR p).mono
      (Set.prod_mono inter_subset_left subset_rfl)).sub
      ((canonicalDomain_contDiffOn_flow_curvature U hU qS F' R' hR' p).mono
        (Set.prod_mono inter_subset_right subset_rfl))
  exact ⟨qH.contDiff.comp_contDiffOn hH, qA.contDiff.comp_contDiffOn hA,
    qS.contDiff.comp_contDiffOn hS⟩

end PoincareConjecture.M34
