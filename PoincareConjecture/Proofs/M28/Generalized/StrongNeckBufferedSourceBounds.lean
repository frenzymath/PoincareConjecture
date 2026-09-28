import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedCurvatureBounds
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedFlow
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedShiBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

theorem exists_strongNeck_buffered_source_bounds_accuracy
    (hShi : LocalCurvatureDerivativeEstimates.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∃ K : ℝ, 0 < K ∧
        ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
          ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
            ∀ (F : GeneralizedRicciFlowData.{u}) (t : ℝ)
              (S : GeneralizedStrongNeck F t epsilon)
              (H : RescaledRawCylinderData (C := F.slice t)
                (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
                (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S)),
              let G := GeneralizedStrongNeck.rescaled_buffered_flow S H
              (∀ s ∈ Icc (-(3 / 4 : ℝ)) 0, ∀ x : strongNeckOpen S,
                (G.connection s).curvatureTensorNorm x ≤ K) ∧
              ∀ m : ℕ, ∀ s ∈ Icc (-(5 / 8 : ℝ)) 0, ∀ q : strongNeckOpen S,
                |(S.coordinate_inverse q.val).2| ≤ 3 * epsilon⁻¹ / 4 →
                  (G.connection s).curvatureDerivativeNorm m q ≤ B m := by
  classical
  obtain ⟨epsilon0, hpos, hsmall, K, hK, hcurvature⟩ :=
    exists_strongNeck_rescaled_buffered_curvature_bound.{u}
  refine ⟨epsilon0, hpos, hsmall, K, hK, ?_⟩
  intro epsilon hepsilon heps
  choose B hB hderiv using
    fun m => exists_source_neck_buffered_core_derivative_bound hShi hepsilon hK m
  refine ⟨B, hB, ?_⟩
  intro F t S H
  let G := GeneralizedStrongNeck.rescaled_buffered_flow S H
  have hRm : ∀ s ∈ Icc (-(3 / 4 : ℝ)) 0, ∀ x : strongNeckOpen S,
      (G.connection s).curvatureTensorNorm x ≤ K :=
    hcurvature F t epsilon S H heps
  refine ⟨hRm, ?_⟩
  have hhalf : epsilon < 1 / 2 := (heps.trans hsmall).trans_lt (by norm_num)
  let N := GeneralizedStrongNeck.rescaled_source_neck S hhalf H
  intro m s hs q hheight
  exact hderiv m (strongNeckOpen S) G N rfl rfl hRm s hs q
    (by change q ∈ (univ : Set (strongNeckOpen S)); exact mem_univ q) hheight

end PoincareConjecture.M28
